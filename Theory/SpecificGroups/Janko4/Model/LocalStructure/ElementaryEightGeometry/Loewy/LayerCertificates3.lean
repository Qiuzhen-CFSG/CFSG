module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Generators
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.TableAccess
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Sparse

/-!
# Checked native layer displacements and mutual span certificates

Literal row actions, forward combinations, and sparse reverse combinations
identify successive canonical spans. Structural chunk-access lemmas ensure
that each kernel calculation traverses only the relevant data block.
Source: KW (1988), Corollary 2.3.6, original 112-dimensional row convention.
-/
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open GeneratorCertificates
private def source3_0Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 0) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(0 : Fin 8)))

attribute [local irreducible] source3_0Pred

private theorem source3_0_0 (i : Fin 8) :
    source3_0Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_0Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 0+8*(0+i.val); omega) (by change 0+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_0_8 (i : Fin 8) :
    source3_0Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_0Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 0+8*(8+i.val); omega) (by change 0+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_0_16 (i : Fin 8) :
    source3_0Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_0Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 0+8*(16+i.val); omega) (by change 0+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_0_24 (i : Fin 8) :
    source3_0Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_0Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 0+8*(24+i.val); omega) (by change 0+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_0_all (i : Fin 32) : source3_0Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_0_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_0_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_0_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_0_24 _

private def source3_1Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 1) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(1 : Fin 8)))

attribute [local irreducible] source3_1Pred

private theorem source3_1_0 (i : Fin 8) :
    source3_1Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_1Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 1+8*(0+i.val); omega) (by change 1+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_1_8 (i : Fin 8) :
    source3_1Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_1Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 1+8*(8+i.val); omega) (by change 1+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_1_16 (i : Fin 8) :
    source3_1Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_1Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 1+8*(16+i.val); omega) (by change 1+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_1_24 (i : Fin 8) :
    source3_1Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_1Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 1+8*(24+i.val); omega) (by change 1+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_1_all (i : Fin 32) : source3_1Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_1_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_1_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_1_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_1_24 _

private def source3_2Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 2) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(2 : Fin 8)))

attribute [local irreducible] source3_2Pred

private theorem source3_2_0 (i : Fin 8) :
    source3_2Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_2Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 2+8*(0+i.val); omega) (by change 2+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_2_8 (i : Fin 8) :
    source3_2Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_2Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 2+8*(8+i.val); omega) (by change 2+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_2_16 (i : Fin 8) :
    source3_2Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_2Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 2+8*(16+i.val); omega) (by change 2+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_2_24 (i : Fin 8) :
    source3_2Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_2Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 2+8*(24+i.val); omega) (by change 2+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_2_all (i : Fin 32) : source3_2Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_2_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_2_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_2_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_2_24 _

private def source3_3Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 3) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(3 : Fin 8)))

attribute [local irreducible] source3_3Pred

private theorem source3_3_0 (i : Fin 8) :
    source3_3Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_3Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 3+8*(0+i.val); omega) (by change 3+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_3_8 (i : Fin 8) :
    source3_3Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_3Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 3+8*(8+i.val); omega) (by change 3+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_3_16 (i : Fin 8) :
    source3_3Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_3Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 3+8*(16+i.val); omega) (by change 3+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_3_24 (i : Fin 8) :
    source3_3Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_3Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 3+8*(24+i.val); omega) (by change 3+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_3_all (i : Fin 32) : source3_3Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_3_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_3_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_3_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_3_24 _

private def source3_4Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 4) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(4 : Fin 8)))

attribute [local irreducible] source3_4Pred

private theorem source3_4_0 (i : Fin 8) :
    source3_4Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_4Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 4+8*(0+i.val); omega) (by change 4+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_4_8 (i : Fin 8) :
    source3_4Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_4Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 4+8*(8+i.val); omega) (by change 4+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_4_16 (i : Fin 8) :
    source3_4Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_4Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 4+8*(16+i.val); omega) (by change 4+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_4_24 (i : Fin 8) :
    source3_4Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_4Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 4+8*(24+i.val); omega) (by change 4+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_4_all (i : Fin 32) : source3_4Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_4_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_4_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_4_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_4_24 _

private def source3_5Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 5) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(5 : Fin 8)))

attribute [local irreducible] source3_5Pred

private theorem source3_5_0 (i : Fin 8) :
    source3_5Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_5Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 5+8*(0+i.val); omega) (by change 5+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_5_8 (i : Fin 8) :
    source3_5Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_5Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 5+8*(8+i.val); omega) (by change 5+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_5_16 (i : Fin 8) :
    source3_5Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_5Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 5+8*(16+i.val); omega) (by change 5+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_5_24 (i : Fin 8) :
    source3_5Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_5Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 5+8*(24+i.val); omega) (by change 5+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_5_all (i : Fin 32) : source3_5Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_5_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_5_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_5_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_5_24 _

private def source3_6Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 6) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(6 : Fin 8)))

attribute [local irreducible] source3_6Pred

private theorem source3_6_0 (i : Fin 8) :
    source3_6Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_6Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 6+8*(0+i.val); omega) (by change 6+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_6_8 (i : Fin 8) :
    source3_6Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_6Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 6+8*(8+i.val); omega) (by change 6+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_6_16 (i : Fin 8) :
    source3_6Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_6Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 6+8*(16+i.val); omega) (by change 6+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_6_24 (i : Fin 8) :
    source3_6Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_6Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 6+8*(24+i.val); omega) (by change 6+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_6_all (i : Fin 32) : source3_6Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_6_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_6_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_6_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_6_24 _

private def source3_7Pred (i : Fin 32) : Prop :=
  packedRow (layer3Rows.get i) (generatorRows 7) ^^^ layer3Rows.get i = step3Rows.get (finProdFinEquiv (i,(7 : Fin 8)))

attribute [local irreducible] source3_7Pred

private theorem source3_7_0 (i : Fin 8) :
    source3_7Pred (Fin.natAdd 0 (Fin.castAdd 24 i)) := by
  unfold source3_7Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 7+8*(0+i.val); omega) (by change 7+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_7_8 (i : Fin 8) :
    source3_7Pred (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  unfold source3_7Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 7+8*(8+i.val); omega) (by change 7+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_7_16 (i : Fin 8) :
    source3_7Pred (Fin.natAdd 16 (Fin.castAdd 8 i)) := by
  unfold source3_7Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 7+8*(16+i.val); omega) (by change 7+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_7_24 (i : Fin 8) :
    source3_7Pred (Fin.natAdd 24 (Fin.castAdd 0 i)) := by
  unfold source3_7Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 7+8*(24+i.val); omega) (by change 7+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source3_7_all (i : Fin 32) : source3_7Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 24 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_7_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 16 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_7_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 8 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source3_7_16 _
  have he : i = (Fin.natAdd 24 (Fin.castAdd 0 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source3_7_24 _

theorem step3_source (i : Fin 32) (j : Fin 8) :
    packedRow (layer3Rows.get i) (generatorRows j) ^^^ layer3Rows.get i =
      step3Rows.get (finProdFinEquiv (i,j)) := by
  have hj : ∀ j : Fin 8, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by decide +kernel
  rcases hj j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [source3_0Pred] using source3_0_all i
  · simpa only [source3_1Pred] using source3_1_all i
  · simpa only [source3_2Pred] using source3_2_all i
  · simpa only [source3_3Pred] using source3_3_all i
  · simpa only [source3_4Pred] using source3_4_all i
  · simpa only [source3_5Pred] using source3_5_all i
  · simpa only [source3_6Pred] using source3_6_all i
  · simpa only [source3_7Pred] using source3_7_all i

private def forward3Pred (i : Fin 256) : Prop :=
  step3Rows.get i = combine layer4Rows (forward3.get i)

attribute [local irreducible] forward3Pred

private theorem forward3_0 (i : Fin 16) :
    forward3Pred (Fin.natAdd 0 (Fin.castAdd 240 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  rw [forward3_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_16 (i : Fin 16) :
    forward3Pred (Fin.natAdd 16 (Fin.castAdd 224 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  rw [forward3_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_32 (i : Fin 16) :
    forward3Pred (Fin.natAdd 32 (Fin.castAdd 208 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  rw [forward3_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_48 (i : Fin 16) :
    forward3Pred (Fin.natAdd 48 (Fin.castAdd 192 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  rw [forward3_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_64 (i : Fin 16) :
    forward3Pred (Fin.natAdd 64 (Fin.castAdd 176 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  rw [forward3_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_80 (i : Fin 16) :
    forward3Pred (Fin.natAdd 80 (Fin.castAdd 160 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  rw [forward3_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_96 (i : Fin 16) :
    forward3Pred (Fin.natAdd 96 (Fin.castAdd 144 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  rw [forward3_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_112 (i : Fin 16) :
    forward3Pred (Fin.natAdd 112 (Fin.castAdd 128 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  rw [forward3_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_128 (i : Fin 16) :
    forward3Pred (Fin.natAdd 128 (Fin.castAdd 112 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  rw [forward3_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_144 (i : Fin 16) :
    forward3Pred (Fin.natAdd 144 (Fin.castAdd 96 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  rw [forward3_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_160 (i : Fin 16) :
    forward3Pred (Fin.natAdd 160 (Fin.castAdd 80 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  rw [forward3_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_176 (i : Fin 16) :
    forward3Pred (Fin.natAdd 176 (Fin.castAdd 64 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  rw [forward3_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_192 (i : Fin 16) :
    forward3Pred (Fin.natAdd 192 (Fin.castAdd 48 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  rw [forward3_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_208 (i : Fin 16) :
    forward3Pred (Fin.natAdd 208 (Fin.castAdd 32 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  rw [forward3_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_224 (i : Fin 16) :
    forward3Pred (Fin.natAdd 224 (Fin.castAdd 16 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  rw [forward3_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_240 (i : Fin 16) :
    forward3Pred (Fin.natAdd 240 (Fin.castAdd 0 i)) := by
  unfold forward3Pred
  rw [step3Rows_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  rw [forward3_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward3_all (i : Fin 256) : forward3Pred i := by
  by_cases h0 : i.val < 16
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 240 (⟨i.val-0, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_0 _
  by_cases h16 : i.val < 32
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 224 (⟨i.val-16, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_16 _
  by_cases h32 : i.val < 48
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 208 (⟨i.val-32, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_32 _
  by_cases h48 : i.val < 64
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 192 (⟨i.val-48, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_48 _
  by_cases h64 : i.val < 80
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 176 (⟨i.val-64, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_64 _
  by_cases h80 : i.val < 96
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 160 (⟨i.val-80, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_80 _
  by_cases h96 : i.val < 112
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 144 (⟨i.val-96, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_96 _
  by_cases h112 : i.val < 128
  · have he : i = (Fin.natAdd 112 (Fin.castAdd 128 (⟨i.val-112, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_112 _
  by_cases h128 : i.val < 144
  · have he : i = (Fin.natAdd 128 (Fin.castAdd 112 (⟨i.val-128, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_128 _
  by_cases h144 : i.val < 160
  · have he : i = (Fin.natAdd 144 (Fin.castAdd 96 (⟨i.val-144, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_144 _
  by_cases h160 : i.val < 176
  · have he : i = (Fin.natAdd 160 (Fin.castAdd 80 (⟨i.val-160, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_160 _
  by_cases h176 : i.val < 192
  · have he : i = (Fin.natAdd 176 (Fin.castAdd 64 (⟨i.val-176, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_176 _
  by_cases h192 : i.val < 208
  · have he : i = (Fin.natAdd 192 (Fin.castAdd 48 (⟨i.val-192, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_192 _
  by_cases h208 : i.val < 224
  · have he : i = (Fin.natAdd 208 (Fin.castAdd 32 (⟨i.val-208, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_208 _
  by_cases h224 : i.val < 240
  · have he : i = (Fin.natAdd 224 (Fin.castAdd 16 (⟨i.val-224, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward3_224 _
  have he : i = (Fin.natAdd 240 (Fin.castAdd 0 (⟨i.val-240, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact forward3_240 _

theorem step3_forward (i : Fin 256) : step3Rows.get i =
    combine layer4Rows (forward3.get i) := by
  simpa only [forward3Pred] using forward3_all i

private def reverse3Pred (i : Fin 4) : Prop :=
  layer4Rows.get i = sparseCombine step3Rows (reverse3Sparse.get i)

attribute [local irreducible] reverse3Pred

private theorem reverse3_0 (i : Fin 4) :
    reverse3Pred (Fin.natAdd 0 (Fin.castAdd 0 i)) := by
  unfold reverse3Pred
  rw [reverse3Sparse_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step3Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse3_all (i : Fin 4) : reverse3Pred i := by
  have he : i = (Fin.natAdd 0 (Fin.castAdd 0 (⟨i.val-0, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact reverse3_0 _

theorem step3_reverse (i : Fin 4) : layer4Rows.get i =
    sparseCombine step3Rows (reverse3Sparse.get i) := by
  simpa only [reverse3Pred] using reverse3_all i

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
