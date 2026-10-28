module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.E7Block.Injection

/-!
# Integral simple operators on the 27-root block

The checked signed steps give complete columns of the literal E7 Geck matrices.
A missing opposite step makes the root-string coefficient one. The basis action
therefore agrees with the published cubic model, including vanishing outside the
block. All assertions are integral, prior to any field specialization.
Source: GLS3 §2.6.2, with the central character of §§1.12.5–6.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Matrix
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _

private theorem root_add_of_some {i : Fin 6} {j k : Fin 27}
    (h : CubicModel.source false i j = some k) :
    typeE7RootPairing.root (root k) = typeE7RootPairing.root (e7Node i) + typeE7RootPairing.root (root j) := by
  apply Subtype.ext
  change coord k = typeE7SimpleRoot (i.castLE (by decide)) + coord j
  have hs := step_of_some (s := true) h
  simpa only [step, Bool.true_eq, ↓reduceIte, add_comm] using hs.symm

private theorem root_sub_of_some {i : Fin 6} {j k : Fin 27}
    (h : CubicModel.source true i j = some k) :
    typeE7RootPairing.root (root k) = typeE7RootPairing.root (root j) - typeE7RootPairing.root (e7Node i) := by
  apply Subtype.ext
  change coord k = coord j - typeE7SimpleRoot (i.castLE (by decide))
  have hs := step_of_some (s := false) h
  simpa only [step, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg] using hs.symm

private theorem root_add_notMem {i : Fin 6} {j : Fin 27}
    (h : CubicModel.source false i j = none) :
    typeE7RootPairing.root (e7Node i) + typeE7RootPairing.root (root j) ∉ Set.range typeE7RootPairing.root := by
  rintro ⟨r, hr⟩
  have hv := congrArg Subtype.val hr
  change r.val = typeE7SimpleRoot (i.castLE (by decide)) + coord j at hv
  apply step_notMem_of_none (s := true) h
  have he : step true i j = r.val := by
    simpa only [step, Bool.true_eq, ↓reduceIte, add_comm] using hv.symm
  rw [he]
  exact r.property

private theorem root_sub_notMem {i : Fin 6} {j : Fin 27}
    (h : CubicModel.source true i j = none) :
    typeE7RootPairing.root (root j) - typeE7RootPairing.root (e7Node i) ∉ Set.range typeE7RootPairing.root := by
  rintro ⟨r, hr⟩
  have hv := congrArg Subtype.val hr
  change r.val = coord j - typeE7SimpleRoot (i.castLE (by decide)) at hv
  apply step_notMem_of_none (s := false) h
  have he : step false i j = r.val := by
    simpa only [step, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg] using hv.symm
  rw [he]
  exact r.property

private theorem root_ne_node (i : Fin 6) (j : Fin 27) : root j ≠ (e7Node i : typeE7Roots) := by
  intro h
  have hv := congrArg (fun r : typeE7Roots => r.val 1 - r.val 2) h
  change coord j 1 - coord j 2 =
    typeE7SimpleRoot (i.castLE (by decide)) 1 - typeE7SimpleRoot (i.castLE (by decide)) 2 at hv
  rw [coord_level, simple_level] at hv
  norm_num at hv

private theorem root_ne_neg_node (i : Fin 6) (j : Fin 27) :
    letI := typeE7RootPairing.indexNeg
    root j ≠ -(e7Node i : typeE7Roots) := by
  intro h
  have hr := congrArg typeE7RootPairing.root h
  change typeE7RootPairing.root (root j) = typeE7RootPairing.root (typeE7RootPairing.reflectionPerm (e7Node i) (e7Node i)) at hr
  rw [typeE7RootPairing.root_reflectionPerm, typeE7RootPairing.reflection_apply_self] at hr
  have hv := congrArg (fun x : typeE7Space => x.val 1 - x.val 2) hr
  change coord j 1 - coord j 2 =
    -typeE7SimpleRoot (i.castLE (by decide)) 1 - -typeE7SimpleRoot (i.castLE (by decide)) 2 at hv
  have hs := simple_level i
  rw [coord_level] at hv
  linarith

/-- The integral matrix with precisely the published source entries. -/
def operatorMatrix (s : Bool) (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  fun k j => if CubicModel.source (!s) i j = some k then 1 else 0

/-- Specializing this integral matrix gives the model's linear operator. -/
theorem operatorMatrix_mulVec (R : Type*) [CommRing R] (s : Bool) (i : Fin 6)
    (x : Fin 27 → R) :
    (operatorMatrix s i).map (Int.castRingHom R) *ᵥ x = CubicModel.operator s i x := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, operatorMatrix,
    ← source_transpose]
  cases h : CubicModel.source s i k with
  | none => simp [h, CubicModel.operator]
  | some j => simp [h, CubicModel.operator]

/-- The integral operator squares to zero. -/
theorem operatorMatrix_square (s : Bool) (i : Fin 6) : operatorMatrix s i ^ 2 = 0 := by
  apply Matrix.mulVec_injective
  funext x
  have hm : (operatorMatrix s i).map (Int.castRingHom ℤ) = operatorMatrix s i := by
    ext k j
    simp
  have h := operatorMatrix_mulVec ℤ s i
  rw [hm] at h
  rw [pow_two, ← Matrix.mulVec_mulVec, h, h, CubicModel.operator_square]
  simp

private theorem e_column (i : Fin 6) (j : Fin 27) :
    eMatrix (e7Node i) *ᵥ v (b := typeE7RootPairing_base) (root j) =
      match CubicModel.source false i j with
      | none => 0
      | some k => v (b := typeE7RootPairing_base) (root k) := by
  cases h : CubicModel.source false i j with
  | none => exact eMatrix_mulVec_v_zero (root_ne_neg_node i j) (root_add_notMem h)
  | some k =>
    rw [eMatrix_mulVec_v_add (root_add_of_some h)]
    have hn := source_disjoint true i j (by simp [h])
    have hc : typeE7RootPairing.chainBotCoeff (e7Node i) (root j) = 0 :=
      typeE7RootPairing.chainBotCoeff_eq_zero_iff.mpr (Or.inr (root_sub_notMem hn))
    simp [hc]

private theorem f_column (i : Fin 6) (j : Fin 27) :
    fMatrix (e7Node i) *ᵥ v (b := typeE7RootPairing_base) (root j) =
      match CubicModel.source true i j with
      | none => 0
      | some k => v (b := typeE7RootPairing_base) (root k) := by
  cases h : CubicModel.source true i j with
  | none => exact fMatrix_mulVec_v_zero (root_ne_node i j) (root_sub_notMem h)
  | some k =>
    rw [fMatrix_mulVec_v_sub (root_sub_of_some h)]
    have hn := source_disjoint false i j (by simp [h])
    have hc : typeE7RootPairing.chainTopCoeff (e7Node i) (root j) = 0 :=
      typeE7RootPairing.chainTopCoeff_eq_zero_iff.mpr (Or.inr (by simpa only [add_comm] using root_add_notMem hn))
    simp [hc]

/-- Both integral signed simple operators intertwine the actual inclusion. -/
theorem operator_intertwines (s : Bool) (i : Fin 6) :
    (if s then eMatrix (e7Node i) else fMatrix (e7Node i)) * AdjointBlocks.inclusion index =
      AdjointBlocks.inclusion index * operatorMatrix s i := by
  ext a j
  have hc : (if s then eMatrix (e7Node i) else fMatrix (e7Node i)) *ᵥ
      v (b := typeE7RootPairing_base) (root j) =
      match CubicModel.source (!s) i j with
      | none => 0
      | some k => v (b := typeE7RootPairing_base) (root k) := by
    cases s
    · exact f_column i j
    · exact e_column i j
  have ha := congrFun hc a
  simp only [v, Matrix.mulVec_single_one] at ha
  have hl : ((if s then eMatrix (e7Node i) else fMatrix (e7Node i)) *
      AdjointBlocks.inclusion index) a j =
      (if s then eMatrix (e7Node i) else fMatrix (e7Node i)) a (index j) := by
    simp [Matrix.mul_apply, AdjointBlocks.inclusion]
  rw [hl]
  cases h : CubicModel.source (!s) i j with
  | none => simpa [Matrix.mul_apply, operatorMatrix, h, index] using ha
  | some k =>
    simpa [Matrix.mul_apply, AdjointBlocks.inclusion, operatorMatrix, h,
      v, Pi.single_apply, index, eq_comm] using ha

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
