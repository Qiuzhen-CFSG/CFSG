module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.Model
public import Theory.AlgebraicGroup.RootSystems.E7RootPairing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The 27 literal E7 root coordinates

The coordinates of the checked cubic are actual, distinct roots of E7. They
lie on the affine level `r₁ - r₂ = -1`. Integer certificates identify the signed
simple-root steps; squared length two excludes all missing steps. This is the
root geometry for the 27-dimensional E6 weight block in the common Chevalley
lattice, GLS3 §2.6.2, used for the central character in §§1.12.5–6 and
Aschbacher–Smith A.2.17 (printed p.39).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block

/-- The real root vector with the published doubled integral coordinates. -/
def coord (j : Fin 27) : Vec 8 := fun k => (CubicModel.twiceRoot j k : ℝ) / 2

private theorem coord_mem_0 : coord 0 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,-2,0,0,0,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 3, by decide, 1, -1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_1 : coord 1 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,-2,0,0,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 4, by decide, 1, -1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_2 : coord 2 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,0,-2,0,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 5, by decide, 1, -1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_3 : coord 3 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,0,0,-2,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 6, by decide, 1, -1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_4 : coord 4 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,0,0,0,-2] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 7, by decide, 1, -1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_5 : coord 5 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,0,0,0,2] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 7, by decide, 1, 1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_6 : coord 6 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,0,0,2,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 6, by decide, 1, 1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_7 : coord 7 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,0,2,0,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 5, by decide, 1, 1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_8 : coord 8 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,0,2,0,0,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 4, by decide, 1, 1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_9 : coord 9 ∈ typeE7Roots := by
  change (fun k => ((![0,0,2,2,0,0,0,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨2, 3, by decide, 1, 1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_10 : coord 10 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,-1,-1,-1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,false,false,false,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_11 : coord 11 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,-1,-1,1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,false,false,true,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_12 : coord 12 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,-1,1,-1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,false,true,false,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_13 : coord 13 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,-1,1,1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,false,true,true,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_14 : coord 14 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,1,-1,-1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,true,false,false,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_15 : coord 15 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,1,-1,1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,true,false,true,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_16 : coord 16 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,1,1,-1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,true,true,false,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_17 : coord 17 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,-1,1,1,1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,false,true,true,true,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_18 : coord 18 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,-1,-1,-1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,false,false,false,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_19 : coord 19 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,-1,-1,1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,false,false,true,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_20 : coord 20 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,-1,1,-1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,false,true,false,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_21 : coord 21 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,-1,1,1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,false,true,true,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_22 : coord 22 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,1,-1,-1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,true,false,false,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_23 : coord 23 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,1,-1,1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,true,false,true,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_24 : coord 24 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,1,1,-1,1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,true,true,false,true], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_25 : coord 25 ∈ typeE7Roots := by
  change (fun k => ((![1,-1,1,1,1,1,1,-1] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · right
    refine ⟨![true,false,true,true,true,true,true,false], ?_, ?_⟩
    · unfold evenNegative
      decide +kernel
    · ext k
      fin_cases k <;> norm_num [halfSignVector]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

private theorem coord_mem_26 : coord 26 ∈ typeE7Roots := by
  change (fun k => ((![2,-2,0,0,0,0,0,0] : Fin 8 → ℤ) k : ℝ) / 2) ∈ typeE7Roots
  constructor
  · left
    refine ⟨0, 1, by decide, 1, -1, by simp, by simp, ?_⟩
    ext k
    fin_cases k <;> norm_num [basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ⬝ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0
    rw [dotProduct_add, dotProduct_single, dotProduct_single]
    norm_num

/-- Every coordinate of the cubic is an actual E7 root. -/
theorem coord_mem (j : Fin 27) : coord j ∈ typeE7Roots := by
  fin_cases j
  · exact coord_mem_0
  · exact coord_mem_1
  · exact coord_mem_2
  · exact coord_mem_3
  · exact coord_mem_4
  · exact coord_mem_5
  · exact coord_mem_6
  · exact coord_mem_7
  · exact coord_mem_8
  · exact coord_mem_9
  · exact coord_mem_10
  · exact coord_mem_11
  · exact coord_mem_12
  · exact coord_mem_13
  · exact coord_mem_14
  · exact coord_mem_15
  · exact coord_mem_16
  · exact coord_mem_17
  · exact coord_mem_18
  · exact coord_mem_19
  · exact coord_mem_20
  · exact coord_mem_21
  · exact coord_mem_22
  · exact coord_mem_23
  · exact coord_mem_24
  · exact coord_mem_25
  · exact coord_mem_26

private theorem twiceRoot_injective : Function.Injective CubicModel.twiceRoot := by
  have h : ∀ i j : Fin 27, (∀ k, CubicModel.twiceRoot i k = CubicModel.twiceRoot j k) → i = j := by
    decide +kernel
  exact fun _ _ he => h _ _ (congrFun he)

/-- The coordinate list has no repetitions. -/
theorem coord_injective : Function.Injective coord := by
  intro i j h
  apply twiceRoot_injective
  funext k
  apply Int.cast_injective (α := ℝ)
  have hk := congrFun h k
  dsimp [coord] at hk
  linarith

/-- The actual root indices, rather than a separate root-system tag. -/
def root : Fin 27 ↪ typeE7Roots where
  toFun j := ⟨coord j, coord_mem j⟩
  inj' _ _ h := coord_injective (congrArg Subtype.val h)

@[simp] theorem root_val (j : Fin 27) : (root j).val = coord j := rfl

/-- The affine E6 level of every vector in the list. -/
theorem coord_level (j : Fin 27) : coord j 1 - coord j 2 = -1 := by
  have hc : ∀ j, CubicModel.twiceRoot j 1 - CubicModel.twiceRoot j 2 = -2 := by
    decide +kernel
  have h := congrArg (fun z : ℤ => (z : ℝ)) (hc j)
  push_cast at h
  dsimp [coord]
  linarith

/-- Twice the first six literal simple roots. -/
def twiceSimple : Fin 6 → Fin 8 → ℤ :=
  ![![1,-1,-1,-1,-1,-1,-1,1], ![0,0,0,0,0,0,2,-2],
    ![0,0,0,0,0,2,-2,0], ![0,0,0,0,0,0,2,2],
    ![0,0,0,0,2,-2,0,0], ![0,0,0,2,-2,0,0,0]]

theorem simple_coord (i : Fin 6) (k : Fin 8) :
    typeE7SimpleRoot (i.castLE (by decide)) k = (twiceSimple i k : ℝ) / 2 := by
  fin_cases i <;> fin_cases k <;>
    norm_num [typeE7SimpleRoot, typeE8SimpleRoot, twiceSimple, Fin.castLE]

theorem simple_level (i : Fin 6) :
    typeE7SimpleRoot (i.castLE (by decide)) 1 -
      typeE7SimpleRoot (i.castLE (by decide)) 2 = 0 := by
  fin_cases i <;> norm_num [typeE7SimpleRoot, typeE8SimpleRoot, Fin.castLE, Matrix.cons_val_two]

/-- The integer coordinates of one signed root step. -/
def twiceStep (s : Bool) (i : Fin 6) (j : Fin 27) (k : Fin 8) : ℤ :=
  CubicModel.twiceRoot j k + if s then twiceSimple i k else -twiceSimple i k

/-- Column targets are the row sources with the sign reversed. -/
theorem source_transpose : ∀ (s : Bool) (i : Fin 6) (j k : Fin 27),
    CubicModel.source s i k = some j ↔ CubicModel.source (!s) i j = some k := by
  decide +kernel

private theorem step_certificate_0 : ∀ (s : Bool) (j : Fin 27),
    (∀ k, CubicModel.source (!s) 0 j = some k →
      ∀ a, twiceStep s 0 j a = CubicModel.twiceRoot k a) ∧
    (CubicModel.source (!s) 0 j = none →
      (∑ k, twiceStep s 0 j k * twiceStep s 0 j k) ≠ 8) := by
  decide +kernel

private theorem step_certificate_1 : ∀ (s : Bool) (j : Fin 27),
    (∀ k, CubicModel.source (!s) 1 j = some k →
      ∀ a, twiceStep s 1 j a = CubicModel.twiceRoot k a) ∧
    (CubicModel.source (!s) 1 j = none →
      (∑ k, twiceStep s 1 j k * twiceStep s 1 j k) ≠ 8) := by
  decide +kernel

private theorem step_certificate_2 : ∀ (s : Bool) (j : Fin 27),
    (∀ k, CubicModel.source (!s) 2 j = some k →
      ∀ a, twiceStep s 2 j a = CubicModel.twiceRoot k a) ∧
    (CubicModel.source (!s) 2 j = none →
      (∑ k, twiceStep s 2 j k * twiceStep s 2 j k) ≠ 8) := by
  decide +kernel

private theorem step_certificate_3 : ∀ (s : Bool) (j : Fin 27),
    (∀ k, CubicModel.source (!s) 3 j = some k →
      ∀ a, twiceStep s 3 j a = CubicModel.twiceRoot k a) ∧
    (CubicModel.source (!s) 3 j = none →
      (∑ k, twiceStep s 3 j k * twiceStep s 3 j k) ≠ 8) := by
  decide +kernel

private theorem step_certificate_4 : ∀ (s : Bool) (j : Fin 27),
    (∀ k, CubicModel.source (!s) 4 j = some k →
      ∀ a, twiceStep s 4 j a = CubicModel.twiceRoot k a) ∧
    (CubicModel.source (!s) 4 j = none →
      (∑ k, twiceStep s 4 j k * twiceStep s 4 j k) ≠ 8) := by
  decide +kernel

private theorem step_certificate_5 : ∀ (s : Bool) (j : Fin 27),
    (∀ k, CubicModel.source (!s) 5 j = some k →
      ∀ a, twiceStep s 5 j a = CubicModel.twiceRoot k a) ∧
    (CubicModel.source (!s) 5 j = none →
      (∑ k, twiceStep s 5 j k * twiceStep s 5 j k) ≠ 8) := by
  decide +kernel

/-- A checked signed step either lands on the listed root or fails squared length two. -/
theorem step_certificate (s : Bool) (i : Fin 6) (j : Fin 27) :
    (∀ k, CubicModel.source (!s) i j = some k →
      ∀ a, twiceStep s i j a = CubicModel.twiceRoot k a) ∧
    (CubicModel.source (!s) i j = none →
      (∑ k, twiceStep s i j k * twiceStep s i j k) ≠ 8) := by
  fin_cases i
  · exact step_certificate_0 s j
  · exact step_certificate_1 s j
  · exact step_certificate_2 s j
  · exact step_certificate_3 s j
  · exact step_certificate_4 s j
  · exact step_certificate_5 s j

/-- The two directions never both leave the same coordinate. -/
theorem source_disjoint : ∀ (s : Bool) (i : Fin 6) (j : Fin 27),
    CubicModel.source (!s) i j ≠ none → CubicModel.source s i j = none := by
  decide +kernel

/-- The real signed simple-root step. -/
def step (s : Bool) (i : Fin 6) (j : Fin 27) : Vec 8 :=
  coord j + if s then typeE7SimpleRoot (i.castLE (by decide))
    else -typeE7SimpleRoot (i.castLE (by decide))

theorem step_coord (s : Bool) (i : Fin 6) (j : Fin 27) (k : Fin 8) :
    step s i j k = (twiceStep s i j k : ℝ) / 2 := by
  cases s <;> simp [step, coord, twiceStep, simple_coord] <;> ring

/-- Every recorded edge is literal addition or subtraction of the simple root. -/
theorem step_of_some {s : Bool} {i : Fin 6} {j k : Fin 27}
    (h : CubicModel.source (!s) i j = some k) : step s i j = coord k := by
  have hc := (step_certificate s i j).1 k h
  funext a
  rw [step_coord, hc]
  rfl

/-- Missing edges cannot reach any other ambient root: their squared length is not two. -/
theorem step_notMem_of_none {s : Bool} {i : Fin 6} {j : Fin 27}
    (h : CubicModel.source (!s) i j = none) : step s i j ∉ typeE7Roots := by
  have hc := (step_certificate s i j).2 h
  intro hm
  have hn := typeE7Root_dot_self ⟨step s i j, hm⟩
  have he : dot (step s i j) (step s i j) =
      ((∑ k, twiceStep s i j k * twiceStep s i j k : ℤ) : ℝ) / 4 := by
    simp only [dot, step_coord, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hn
  apply hc
  apply Int.cast_injective (α := ℝ)
  norm_num only [Int.cast_ofNat]
  linarith

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7Block
