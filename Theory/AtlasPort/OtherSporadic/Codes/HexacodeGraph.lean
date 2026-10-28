/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeMDS

/-!
# HexacodeGraph

An MDS code is expressed as the graph of a matrix of Kleinian isometries. Rescaling its
coordinates normalizes the first row and column while preserving the graph minimum-
weight condition.

Source: `Atlas/Codes/HexacodeGraph.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

abbrev KleinMatrix := Fin 3 → Fin 3 → KIsometry

def kleinGraphWord (M : KleinMatrix) (x : Fin 3 → K) : HexWord :=
  fun p => Fin.addCases x (fun i => ∑ j, M i j (x j)) (hexIndexEquiv p)

@[simp] theorem kleinGraphWord_first (M : KleinMatrix) (x : Fin 3 → K) (i : Fin 3) :
    kleinGraphWord M x (firstThree i) = x i := by
  simp [kleinGraphWord,firstThree,hexPos]

@[simp] theorem kleinGraphWord_last (M : KleinMatrix) (x : Fin 3 → K) (i : Fin 3) :
    kleinGraphWord M x (lastThree i) = ∑ j, M i j (x j) := by
  change Fin.addCases (motive := fun _ : Fin 6 => K) x (fun i => ∑ j, M i j (x j))
      (hexIndexEquiv (hexPos (Fin.natAdd 3 i))) = _
  rw [index_hexPos]
  exact Fin.addCases_right i

theorem hexIndex_first_or_last : ∀ p : HexIndex,
    (∃ i, p = firstThree i) ∨ (∃ i, p = lastThree i) := by decide

/-- The three-position kernel property of the graph; no classification is assumed. -/
def IsMDSMatrix (M : KleinMatrix) : Prop :=
  ∀ (x : Fin 3 → K) (i j k : HexIndex), i ≠ j → i ≠ k → j ≠ k →
    kleinGraphWord M x i = 0 → kleinGraphWord M x j = 0 → kleinGraphWord M x k = 0 → x = 0

theorem mdsEncoder_graph (D : Submodule Bit HexWord) (hD : IsHexMDS D) (x : Fin 3 → K) :
    mdsEncoder D hD x = kleinGraphWord (mdsCoefficientEquiv D hD) x := by
  funext p
  rcases hexIndex_first_or_last p with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · simp
  · simp [mdsEncoder_last]

theorem mdsMatrix_valid (D : Submodule Bit HexWord) (hD : IsHexMDS D) :
    IsMDSMatrix (mdsCoefficientEquiv D hD) := by
  intro x i j k hij hik hjk hi hj hk
  have hw := code_three_zeros D hD ((mdsInputEquiv D hD).symm x) i j k hij hik hjk
    (by change mdsEncoder D hD x i = 0; rwa [mdsEncoder_graph])
    (by change mdsEncoder D hD x j = 0; rwa [mdsEncoder_graph])
    (by change mdsEncoder D hD x k = 0; rwa [mdsEncoder_graph])
  have he := congrArg (mdsInputEquiv D hD) hw
  simpa using he

def normalizedKleinMatrix (M : KleinMatrix) : KleinMatrix :=
  fun i j => M 0 0 * (M i 0)⁻¹ * M i j * (M 0 j)⁻¹

@[simp] theorem normalizedKleinMatrix_row (M : KleinMatrix) (j : Fin 3) :
    normalizedKleinMatrix M 0 j = 1 := by simp [normalizedKleinMatrix]

@[simp] theorem normalizedKleinMatrix_col (M : KleinMatrix) (i : Fin 3) :
    normalizedKleinMatrix M i 0 = 1 := by simp [normalizedKleinMatrix,mul_assoc]

def kleinNormalization (M : KleinMatrix) : Monomial HexIndex where
  perm := 1
  localMap p := Fin.addCases (fun j => M 0 j) (fun i => M 0 0 * (M i 0)⁻¹) (hexIndexEquiv p)

@[simp] theorem kleinNormalization_first (M : KleinMatrix) (j : Fin 3) :
    (kleinNormalization M).localMap (firstThree j) = M 0 j := by
  simp [kleinNormalization,firstThree,hexPos]
@[simp] theorem kleinNormalization_last (M : KleinMatrix) (i : Fin 3) :
    (kleinNormalization M).localMap (lastThree i) = M 0 0 * (M i 0)⁻¹ := by
  change Fin.addCases (motive := fun _ : Fin 6 => KIsometry) (fun j => M 0 j) (fun i => M 0 0 * (M i 0)⁻¹)
      (hexIndexEquiv (hexPos (Fin.natAdd 3 i))) = _
  rw [index_hexPos]
  exact Fin.addCases_right i

theorem kleinGraph_normalization (M : KleinMatrix) (x : Fin 3 → K) :
    kleinGraphWord (normalizedKleinMatrix M) x =
      Monomial.act (kleinNormalization M) (kleinGraphWord M (fun j => (M 0 j)⁻¹ (x j))) := by
  funext p
  rcases hexIndex_first_or_last p with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · change kleinGraphWord (normalizedKleinMatrix M) x (firstThree i) =
      (kleinNormalization M).localMap (firstThree i)
        (kleinGraphWord M (fun j => (M 0 j)⁻¹ (x j)) (firstThree i))
    simp
  · simp only [Monomial.act_apply]
    change kleinGraphWord (normalizedKleinMatrix M) x (lastThree i) =
      (kleinNormalization M).localMap (lastThree i)
        (kleinGraphWord M (fun j => (M 0 j)⁻¹ (x j)) (lastThree i))
    simp only [kleinGraphWord_last,kleinNormalization_last,map_sum,normalizedKleinMatrix,
      LinearEquiv.mul_apply]

theorem normalizedKleinMatrix_valid (M : KleinMatrix) (hM : IsMDSMatrix M) :
    IsMDSMatrix (normalizedKleinMatrix M) := by
  intro x i j k hij hik hjk hi hj hk
  have zero_back (p : HexIndex) (hp : kleinGraphWord (normalizedKleinMatrix M) x p = 0) :
      kleinGraphWord M (fun j => (M 0 j)⁻¹ (x j)) p = 0 := by
    rw [kleinGraph_normalization] at hp
    exact ((kleinNormalization M).localMap p).map_eq_zero_iff.mp hp
  have hx := hM _ i j k hij hik hjk (zero_back i hi) (zero_back j hj) (zero_back k hk)
  funext l
  exact (M 0 l)⁻¹.map_eq_zero_iff.mp (congrFun hx l)

end Atlas.Codes
