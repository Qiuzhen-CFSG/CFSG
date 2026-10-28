/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineMonomial
public import Theory.AtlasPort.OtherSporadic.Mathieu.AffinePlaneGroup

/-!
# PartitionAffineNormalForm

Every coordinate permutation preserving the tetrad partition has unique affine monomial
parameters. Its induced column permutation and four-point row permutations determine the
translation and local linear maps, and the coordinate formula reconstructs it.

Source: `Atlas/Mathieu/PartitionAffineNormalForm.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open Finset

def PreservesTetradPartition (σ : Equiv.Perm Omega) : Prop :=
  permuteSextetParts σ distinguishedUnorderedSextet.val = distinguishedUnorderedSextet.val

theorem partition_image_tetrad (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ)
    (i : HexIndex) : ∃ j, permuteBlock σ (tetrad i) = tetrad j := by
  classical
  have hi : tetrad i ∈ distinguishedUnorderedSextet.val := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have hh : permuteBlock σ (tetrad i) ∈ distinguishedUnorderedSextet.val := by
    rw [← hσ]
    exact mem_image.mpr ⟨tetrad i,hi,rfl⟩
  obtain ⟨j,_,hj⟩ := mem_image.mp hh
  exact ⟨j,hj.symm⟩

def partitionColumn (σ : Equiv.Perm Omega) (i : HexIndex) : HexIndex := (σ (i,0)).1

def partitionRow (σ : Equiv.Perm Omega) (i : HexIndex) (k : Fin 4) : Fin 4 := (σ (i,k)).2

theorem partition_first_coordinate (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ)
    (i : HexIndex) (k : Fin 4) : (σ (i,k)).1 = partitionColumn σ i := by
  obtain ⟨j,hj⟩ := partition_image_tetrad σ hσ i
  have h (l : Fin 4) : (σ (i,l)).1 = j := by
    apply (mem_tetrad _ _).mp
    rw [← hj]
    exact mem_image.mpr ⟨(i,l),(mem_tetrad _ _).mpr rfl,rfl⟩
  exact (h k).trans (h 0).symm

theorem partitionRow_injective (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ)
    (i : HexIndex) : Function.Injective (partitionRow σ i) := by
  intro k l h
  have he : σ (i,k) = σ (i,l) := Prod.ext
    ((partition_first_coordinate σ hσ i k).trans (partition_first_coordinate σ hσ i l).symm) h
  exact congrArg Prod.snd (σ.injective he)

noncomputable def partitionRowEquiv (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ)
    (i : HexIndex) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (partitionRow σ i)
    ⟨partitionRow_injective σ hσ i,Finite.surjective_of_injective (partitionRow_injective σ hσ i)⟩

theorem partitionColumn_injective (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ) :
    Function.Injective (partitionColumn σ) := by
  intro i j hij
  obtain ⟨k,hk⟩ := (partitionRowEquiv σ hσ j).surjective (partitionRow σ i 0)
  have he : σ (i,0) = σ (j,k) := Prod.ext
    ((partition_first_coordinate σ hσ i 0).trans (hij.trans (partition_first_coordinate σ hσ j k).symm)) hk.symm
  exact congrArg Prod.fst (σ.injective he)

noncomputable def partitionColumnEquiv (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ) :
    Equiv.Perm HexIndex := Equiv.ofBijective (partitionColumn σ)
      ⟨partitionColumn_injective σ hσ,Finite.surjective_of_injective (partitionColumn_injective σ hσ)⟩

noncomputable def partitionRowLabels (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ)
    (j : HexIndex) : Equiv.Perm K :=
  (rowLabel.symm.trans (partitionRowEquiv σ hσ ((partitionColumnEquiv σ hσ).symm j))).trans rowLabel

@[simp] theorem partitionRowLabels_apply (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ)
    (j : HexIndex) (z : K) : partitionRowLabels σ hσ j z =
      rowLabel ((σ ((partitionColumnEquiv σ hσ).symm j,rowLabel.symm z)).2) := rfl

noncomputable def partitionTranslation (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ) : HexWord :=
  fun j => partitionRowLabels σ hσ j 0

noncomputable def partitionMonomial (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ) :
    Monomial HexIndex :=
  ⟨partitionColumnEquiv σ hσ,fun j => rowLinearPart (partitionRowLabels σ hσ j)⟩

theorem partition_affine_reconstruction (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ) :
    affinePermutation (partitionTranslation σ hσ) (partitionMonomial σ hσ) = σ := by
  apply Equiv.ext
  rintro ⟨i,k⟩
  apply Prod.ext
  · exact (partition_first_coordinate σ hσ i k).symm
  · apply rowLabel.injective
    change rowLabel (rowLabel.symm
      (rowLinearPart (partitionRowLabels σ hσ (partitionColumnEquiv σ hσ i)) (rowLabel k) +
        partitionRowLabels σ hσ (partitionColumnEquiv σ hσ i) 0)) = _
    rw [rowLabel.apply_symm_apply,row_affine_formula,partitionRowLabels_apply,
      rowLabel.symm_apply_apply,(partitionColumnEquiv σ hσ).symm_apply_apply]

theorem partition_affine_unique (σ : Equiv.Perm Omega) (hσ : PreservesTetradPartition σ) :
    ∃! x : HexWord × Monomial HexIndex, affinePermutation x.1 x.2 = σ := by
  refine ⟨(partitionTranslation σ hσ,partitionMonomial σ hσ),partition_affine_reconstruction σ hσ,?_⟩
  intro x hx
  exact affinePermutation_injective (hx.trans (partition_affine_reconstruction σ hσ).symm)

end Atlas.Codes
