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
private def source2_0Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 0) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(0 : Fin 8)))

attribute [local irreducible] source2_0Pred

private theorem source2_0_0 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 0+8*(0+i.val); omega) (by change 0+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_8 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 0+8*(8+i.val); omega) (by change 0+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_16 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 0+8*(16+i.val); omega) (by change 0+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_24 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 0+8*(24+i.val); omega) (by change 0+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_32 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 0+8*(32+i.val); omega) (by change 0+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_40 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 0+8*(40+i.val); omega) (by change 0+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_48 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 0+8*(48+i.val); omega) (by change 0+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_56 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 0+8*(56+i.val); omega) (by change 0+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_64 (i : Fin 8) :
    source2_0Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 0+8*(64+i.val); omega) (by change 0+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_72 (i : Fin 4) :
    source2_0Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_0Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 0+8*(72+i.val); omega) (by change 0+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_0_all (i : Fin 76) : source2_0Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_0_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_0_72 _

private def source2_1Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 1) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(1 : Fin 8)))

attribute [local irreducible] source2_1Pred

private theorem source2_1_0 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 1+8*(0+i.val); omega) (by change 1+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_8 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 1+8*(8+i.val); omega) (by change 1+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_16 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 1+8*(16+i.val); omega) (by change 1+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_24 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 1+8*(24+i.val); omega) (by change 1+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_32 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 1+8*(32+i.val); omega) (by change 1+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_40 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 1+8*(40+i.val); omega) (by change 1+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_48 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 1+8*(48+i.val); omega) (by change 1+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_56 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 1+8*(56+i.val); omega) (by change 1+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_64 (i : Fin 8) :
    source2_1Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 1+8*(64+i.val); omega) (by change 1+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_72 (i : Fin 4) :
    source2_1Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_1Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 1+8*(72+i.val); omega) (by change 1+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_1_all (i : Fin 76) : source2_1Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_1_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_1_72 _

private def source2_2Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 2) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(2 : Fin 8)))

attribute [local irreducible] source2_2Pred

private theorem source2_2_0 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 2+8*(0+i.val); omega) (by change 2+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_8 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 2+8*(8+i.val); omega) (by change 2+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_16 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 2+8*(16+i.val); omega) (by change 2+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_24 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 2+8*(24+i.val); omega) (by change 2+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_32 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 2+8*(32+i.val); omega) (by change 2+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_40 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 2+8*(40+i.val); omega) (by change 2+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_48 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 2+8*(48+i.val); omega) (by change 2+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_56 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 2+8*(56+i.val); omega) (by change 2+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_64 (i : Fin 8) :
    source2_2Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 2+8*(64+i.val); omega) (by change 2+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_72 (i : Fin 4) :
    source2_2Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_2Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 2+8*(72+i.val); omega) (by change 2+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_2_all (i : Fin 76) : source2_2Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_2_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_2_72 _

private def source2_3Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 3) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(3 : Fin 8)))

attribute [local irreducible] source2_3Pred

private theorem source2_3_0 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 3+8*(0+i.val); omega) (by change 3+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_8 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 3+8*(8+i.val); omega) (by change 3+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_16 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 3+8*(16+i.val); omega) (by change 3+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_24 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 3+8*(24+i.val); omega) (by change 3+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_32 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 3+8*(32+i.val); omega) (by change 3+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_40 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 3+8*(40+i.val); omega) (by change 3+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_48 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 3+8*(48+i.val); omega) (by change 3+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_56 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 3+8*(56+i.val); omega) (by change 3+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_64 (i : Fin 8) :
    source2_3Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 3+8*(64+i.val); omega) (by change 3+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_72 (i : Fin 4) :
    source2_3Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_3Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 3+8*(72+i.val); omega) (by change 3+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_3_all (i : Fin 76) : source2_3Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_3_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_3_72 _

private def source2_4Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 4) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(4 : Fin 8)))

attribute [local irreducible] source2_4Pred

private theorem source2_4_0 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 4+8*(0+i.val); omega) (by change 4+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_8 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 4+8*(8+i.val); omega) (by change 4+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_16 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 4+8*(16+i.val); omega) (by change 4+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_24 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 4+8*(24+i.val); omega) (by change 4+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_32 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 4+8*(32+i.val); omega) (by change 4+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_40 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 4+8*(40+i.val); omega) (by change 4+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_48 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 4+8*(48+i.val); omega) (by change 4+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_56 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 4+8*(56+i.val); omega) (by change 4+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_64 (i : Fin 8) :
    source2_4Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 4+8*(64+i.val); omega) (by change 4+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_72 (i : Fin 4) :
    source2_4Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_4Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 4+8*(72+i.val); omega) (by change 4+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_4_all (i : Fin 76) : source2_4Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_4_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_4_72 _

private def source2_5Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 5) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(5 : Fin 8)))

attribute [local irreducible] source2_5Pred

private theorem source2_5_0 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 5+8*(0+i.val); omega) (by change 5+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_8 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 5+8*(8+i.val); omega) (by change 5+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_16 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 5+8*(16+i.val); omega) (by change 5+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_24 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 5+8*(24+i.val); omega) (by change 5+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_32 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 5+8*(32+i.val); omega) (by change 5+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_40 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 5+8*(40+i.val); omega) (by change 5+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_48 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 5+8*(48+i.val); omega) (by change 5+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_56 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 5+8*(56+i.val); omega) (by change 5+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_64 (i : Fin 8) :
    source2_5Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 5+8*(64+i.val); omega) (by change 5+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_72 (i : Fin 4) :
    source2_5Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_5Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 5+8*(72+i.val); omega) (by change 5+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_5_all (i : Fin 76) : source2_5Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_5_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_5_72 _

private def source2_6Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 6) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(6 : Fin 8)))

attribute [local irreducible] source2_6Pred

private theorem source2_6_0 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 6+8*(0+i.val); omega) (by change 6+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_8 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 6+8*(8+i.val); omega) (by change 6+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_16 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 6+8*(16+i.val); omega) (by change 6+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_24 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 6+8*(24+i.val); omega) (by change 6+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_32 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 6+8*(32+i.val); omega) (by change 6+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_40 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 6+8*(40+i.val); omega) (by change 6+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_48 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 6+8*(48+i.val); omega) (by change 6+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_56 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 6+8*(56+i.val); omega) (by change 6+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_64 (i : Fin 8) :
    source2_6Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 6+8*(64+i.val); omega) (by change 6+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_72 (i : Fin 4) :
    source2_6Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_6Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 6+8*(72+i.val); omega) (by change 6+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_6_all (i : Fin 76) : source2_6Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_6_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_6_72 _

private def source2_7Pred (i : Fin 76) : Prop :=
  packedRow (layer2Rows.get i) (generatorRows 7) ^^^ layer2Rows.get i = step2Rows.get (finProdFinEquiv (i,(7 : Fin 8)))

attribute [local irreducible] source2_7Pred

private theorem source2_7_0 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 0 (Fin.castAdd 68 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 7+8*(0+i.val); omega) (by change 7+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_8 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 8 (Fin.castAdd 60 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 7+8*(8+i.val); omega) (by change 7+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_16 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 16 (Fin.castAdd 52 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 7+8*(16+i.val); omega) (by change 7+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_24 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 24 (Fin.castAdd 44 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 7+8*(24+i.val); omega) (by change 7+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_32 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 32 (Fin.castAdd 36 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 7+8*(32+i.val); omega) (by change 7+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_40 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 40 (Fin.castAdd 28 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 7+8*(40+i.val); omega) (by change 7+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_48 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 48 (Fin.castAdd 20 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 7+8*(48+i.val); omega) (by change 7+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_56 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 56 (Fin.castAdd 12 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 7+8*(56+i.val); omega) (by change 7+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_64 (i : Fin 8) :
    source2_7Pred (Fin.natAdd 64 (Fin.castAdd 4 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 7+8*(64+i.val); omega) (by change 7+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_72 (i : Fin 4) :
    source2_7Pred (Fin.natAdd 72 (Fin.castAdd 0 i)) := by
  unfold source2_7Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 7+8*(72+i.val); omega) (by change 7+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source2_7_all (i : Fin 76) : source2_7Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 68 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 60 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 52 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 44 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 36 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 28 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 20 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 12 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 4 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source2_7_64 _
  have he : i = (Fin.natAdd 72 (Fin.castAdd 0 (⟨i.val-72, by omega⟩ : Fin 4))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source2_7_72 _

theorem step2_source (i : Fin 76) (j : Fin 8) :
    packedRow (layer2Rows.get i) (generatorRows j) ^^^ layer2Rows.get i =
      step2Rows.get (finProdFinEquiv (i,j)) := by
  have hj : ∀ j : Fin 8, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by decide +kernel
  rcases hj j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [source2_0Pred] using source2_0_all i
  · simpa only [source2_1Pred] using source2_1_all i
  · simpa only [source2_2Pred] using source2_2_all i
  · simpa only [source2_3Pred] using source2_3_all i
  · simpa only [source2_4Pred] using source2_4_all i
  · simpa only [source2_5Pred] using source2_5_all i
  · simpa only [source2_6Pred] using source2_6_all i
  · simpa only [source2_7Pred] using source2_7_all i

private def forward2Pred (i : Fin 608) : Prop :=
  step2Rows.get i = combine layer3Rows (forward2.get i)

attribute [local irreducible] forward2Pred

private theorem forward2_0 (i : Fin 16) :
    forward2Pred (Fin.natAdd 0 (Fin.castAdd 592 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  rw [forward2_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_16 (i : Fin 16) :
    forward2Pred (Fin.natAdd 16 (Fin.castAdd 576 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  rw [forward2_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_32 (i : Fin 16) :
    forward2Pred (Fin.natAdd 32 (Fin.castAdd 560 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  rw [forward2_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_48 (i : Fin 16) :
    forward2Pred (Fin.natAdd 48 (Fin.castAdd 544 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  rw [forward2_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_64 (i : Fin 16) :
    forward2Pred (Fin.natAdd 64 (Fin.castAdd 528 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  rw [forward2_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_80 (i : Fin 16) :
    forward2Pred (Fin.natAdd 80 (Fin.castAdd 512 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  rw [forward2_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_96 (i : Fin 16) :
    forward2Pred (Fin.natAdd 96 (Fin.castAdd 496 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  rw [forward2_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_112 (i : Fin 16) :
    forward2Pred (Fin.natAdd 112 (Fin.castAdd 480 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  rw [forward2_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_128 (i : Fin 16) :
    forward2Pred (Fin.natAdd 128 (Fin.castAdd 464 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  rw [forward2_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_144 (i : Fin 16) :
    forward2Pred (Fin.natAdd 144 (Fin.castAdd 448 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  rw [forward2_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_160 (i : Fin 16) :
    forward2Pred (Fin.natAdd 160 (Fin.castAdd 432 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  rw [forward2_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_176 (i : Fin 16) :
    forward2Pred (Fin.natAdd 176 (Fin.castAdd 416 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  rw [forward2_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_192 (i : Fin 16) :
    forward2Pred (Fin.natAdd 192 (Fin.castAdd 400 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  rw [forward2_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_208 (i : Fin 16) :
    forward2Pred (Fin.natAdd 208 (Fin.castAdd 384 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  rw [forward2_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_224 (i : Fin 16) :
    forward2Pred (Fin.natAdd 224 (Fin.castAdd 368 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  rw [forward2_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_240 (i : Fin 16) :
    forward2Pred (Fin.natAdd 240 (Fin.castAdd 352 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  rw [forward2_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_256 (i : Fin 16) :
    forward2Pred (Fin.natAdd 256 (Fin.castAdd 336 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 256+i.val; omega) (by change 256+i.val < _; omega)]
  rw [forward2_chunk4 _ (by change _ ≤ 256+i.val; omega) (by change 256+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_272 (i : Fin 16) :
    forward2Pred (Fin.natAdd 272 (Fin.castAdd 320 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 272+i.val; omega) (by change 272+i.val < _; omega)]
  rw [forward2_chunk4 _ (by change _ ≤ 272+i.val; omega) (by change 272+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_288 (i : Fin 16) :
    forward2Pred (Fin.natAdd 288 (Fin.castAdd 304 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 288+i.val; omega) (by change 288+i.val < _; omega)]
  rw [forward2_chunk4 _ (by change _ ≤ 288+i.val; omega) (by change 288+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_304 (i : Fin 16) :
    forward2Pred (Fin.natAdd 304 (Fin.castAdd 288 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk4 _ (by change _ ≤ 304+i.val; omega) (by change 304+i.val < _; omega)]
  rw [forward2_chunk4 _ (by change _ ≤ 304+i.val; omega) (by change 304+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_320 (i : Fin 16) :
    forward2Pred (Fin.natAdd 320 (Fin.castAdd 272 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 320+i.val; omega) (by change 320+i.val < _; omega)]
  rw [forward2_chunk5 _ (by change _ ≤ 320+i.val; omega) (by change 320+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_336 (i : Fin 16) :
    forward2Pred (Fin.natAdd 336 (Fin.castAdd 256 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 336+i.val; omega) (by change 336+i.val < _; omega)]
  rw [forward2_chunk5 _ (by change _ ≤ 336+i.val; omega) (by change 336+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_352 (i : Fin 16) :
    forward2Pred (Fin.natAdd 352 (Fin.castAdd 240 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 352+i.val; omega) (by change 352+i.val < _; omega)]
  rw [forward2_chunk5 _ (by change _ ≤ 352+i.val; omega) (by change 352+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_368 (i : Fin 16) :
    forward2Pred (Fin.natAdd 368 (Fin.castAdd 224 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk5 _ (by change _ ≤ 368+i.val; omega) (by change 368+i.val < _; omega)]
  rw [forward2_chunk5 _ (by change _ ≤ 368+i.val; omega) (by change 368+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_384 (i : Fin 16) :
    forward2Pred (Fin.natAdd 384 (Fin.castAdd 208 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 384+i.val; omega) (by change 384+i.val < _; omega)]
  rw [forward2_chunk6 _ (by change _ ≤ 384+i.val; omega) (by change 384+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_400 (i : Fin 16) :
    forward2Pred (Fin.natAdd 400 (Fin.castAdd 192 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 400+i.val; omega) (by change 400+i.val < _; omega)]
  rw [forward2_chunk6 _ (by change _ ≤ 400+i.val; omega) (by change 400+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_416 (i : Fin 16) :
    forward2Pred (Fin.natAdd 416 (Fin.castAdd 176 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 416+i.val; omega) (by change 416+i.val < _; omega)]
  rw [forward2_chunk6 _ (by change _ ≤ 416+i.val; omega) (by change 416+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_432 (i : Fin 16) :
    forward2Pred (Fin.natAdd 432 (Fin.castAdd 160 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk6 _ (by change _ ≤ 432+i.val; omega) (by change 432+i.val < _; omega)]
  rw [forward2_chunk6 _ (by change _ ≤ 432+i.val; omega) (by change 432+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_448 (i : Fin 16) :
    forward2Pred (Fin.natAdd 448 (Fin.castAdd 144 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 448+i.val; omega) (by change 448+i.val < _; omega)]
  rw [forward2_chunk7 _ (by change _ ≤ 448+i.val; omega) (by change 448+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_464 (i : Fin 16) :
    forward2Pred (Fin.natAdd 464 (Fin.castAdd 128 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 464+i.val; omega) (by change 464+i.val < _; omega)]
  rw [forward2_chunk7 _ (by change _ ≤ 464+i.val; omega) (by change 464+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_480 (i : Fin 16) :
    forward2Pred (Fin.natAdd 480 (Fin.castAdd 112 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 480+i.val; omega) (by change 480+i.val < _; omega)]
  rw [forward2_chunk7 _ (by change _ ≤ 480+i.val; omega) (by change 480+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_496 (i : Fin 16) :
    forward2Pred (Fin.natAdd 496 (Fin.castAdd 96 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk7 _ (by change _ ≤ 496+i.val; omega) (by change 496+i.val < _; omega)]
  rw [forward2_chunk7 _ (by change _ ≤ 496+i.val; omega) (by change 496+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_512 (i : Fin 16) :
    forward2Pred (Fin.natAdd 512 (Fin.castAdd 80 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 512+i.val; omega) (by change 512+i.val < _; omega)]
  rw [forward2_chunk8 _ (by change _ ≤ 512+i.val; omega) (by change 512+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_528 (i : Fin 16) :
    forward2Pred (Fin.natAdd 528 (Fin.castAdd 64 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 528+i.val; omega) (by change 528+i.val < _; omega)]
  rw [forward2_chunk8 _ (by change _ ≤ 528+i.val; omega) (by change 528+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_544 (i : Fin 16) :
    forward2Pred (Fin.natAdd 544 (Fin.castAdd 48 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 544+i.val; omega) (by change 544+i.val < _; omega)]
  rw [forward2_chunk8 _ (by change _ ≤ 544+i.val; omega) (by change 544+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_560 (i : Fin 16) :
    forward2Pred (Fin.natAdd 560 (Fin.castAdd 32 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk8 _ (by change _ ≤ 560+i.val; omega) (by change 560+i.val < _; omega)]
  rw [forward2_chunk8 _ (by change _ ≤ 560+i.val; omega) (by change 560+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_576 (i : Fin 16) :
    forward2Pred (Fin.natAdd 576 (Fin.castAdd 16 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 576+i.val; omega) (by change 576+i.val < _; omega)]
  rw [forward2_chunk9 _ (by change _ ≤ 576+i.val; omega) (by change 576+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_592 (i : Fin 16) :
    forward2Pred (Fin.natAdd 592 (Fin.castAdd 0 i)) := by
  unfold forward2Pred
  rw [step2Rows_chunk9 _ (by change _ ≤ 592+i.val; omega) (by change 592+i.val < _; omega)]
  rw [forward2_chunk9 _ (by change _ ≤ 592+i.val; omega) (by change 592+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward2_all (i : Fin 608) : forward2Pred i := by
  by_cases h0 : i.val < 16
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 592 (⟨i.val-0, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_0 _
  by_cases h16 : i.val < 32
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 576 (⟨i.val-16, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_16 _
  by_cases h32 : i.val < 48
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 560 (⟨i.val-32, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_32 _
  by_cases h48 : i.val < 64
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 544 (⟨i.val-48, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_48 _
  by_cases h64 : i.val < 80
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 528 (⟨i.val-64, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_64 _
  by_cases h80 : i.val < 96
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 512 (⟨i.val-80, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_80 _
  by_cases h96 : i.val < 112
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 496 (⟨i.val-96, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_96 _
  by_cases h112 : i.val < 128
  · have he : i = (Fin.natAdd 112 (Fin.castAdd 480 (⟨i.val-112, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_112 _
  by_cases h128 : i.val < 144
  · have he : i = (Fin.natAdd 128 (Fin.castAdd 464 (⟨i.val-128, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_128 _
  by_cases h144 : i.val < 160
  · have he : i = (Fin.natAdd 144 (Fin.castAdd 448 (⟨i.val-144, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_144 _
  by_cases h160 : i.val < 176
  · have he : i = (Fin.natAdd 160 (Fin.castAdd 432 (⟨i.val-160, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_160 _
  by_cases h176 : i.val < 192
  · have he : i = (Fin.natAdd 176 (Fin.castAdd 416 (⟨i.val-176, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_176 _
  by_cases h192 : i.val < 208
  · have he : i = (Fin.natAdd 192 (Fin.castAdd 400 (⟨i.val-192, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_192 _
  by_cases h208 : i.val < 224
  · have he : i = (Fin.natAdd 208 (Fin.castAdd 384 (⟨i.val-208, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_208 _
  by_cases h224 : i.val < 240
  · have he : i = (Fin.natAdd 224 (Fin.castAdd 368 (⟨i.val-224, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_224 _
  by_cases h240 : i.val < 256
  · have he : i = (Fin.natAdd 240 (Fin.castAdd 352 (⟨i.val-240, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_240 _
  by_cases h256 : i.val < 272
  · have he : i = (Fin.natAdd 256 (Fin.castAdd 336 (⟨i.val-256, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_256 _
  by_cases h272 : i.val < 288
  · have he : i = (Fin.natAdd 272 (Fin.castAdd 320 (⟨i.val-272, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_272 _
  by_cases h288 : i.val < 304
  · have he : i = (Fin.natAdd 288 (Fin.castAdd 304 (⟨i.val-288, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_288 _
  by_cases h304 : i.val < 320
  · have he : i = (Fin.natAdd 304 (Fin.castAdd 288 (⟨i.val-304, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_304 _
  by_cases h320 : i.val < 336
  · have he : i = (Fin.natAdd 320 (Fin.castAdd 272 (⟨i.val-320, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_320 _
  by_cases h336 : i.val < 352
  · have he : i = (Fin.natAdd 336 (Fin.castAdd 256 (⟨i.val-336, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_336 _
  by_cases h352 : i.val < 368
  · have he : i = (Fin.natAdd 352 (Fin.castAdd 240 (⟨i.val-352, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_352 _
  by_cases h368 : i.val < 384
  · have he : i = (Fin.natAdd 368 (Fin.castAdd 224 (⟨i.val-368, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_368 _
  by_cases h384 : i.val < 400
  · have he : i = (Fin.natAdd 384 (Fin.castAdd 208 (⟨i.val-384, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_384 _
  by_cases h400 : i.val < 416
  · have he : i = (Fin.natAdd 400 (Fin.castAdd 192 (⟨i.val-400, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_400 _
  by_cases h416 : i.val < 432
  · have he : i = (Fin.natAdd 416 (Fin.castAdd 176 (⟨i.val-416, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_416 _
  by_cases h432 : i.val < 448
  · have he : i = (Fin.natAdd 432 (Fin.castAdd 160 (⟨i.val-432, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_432 _
  by_cases h448 : i.val < 464
  · have he : i = (Fin.natAdd 448 (Fin.castAdd 144 (⟨i.val-448, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_448 _
  by_cases h464 : i.val < 480
  · have he : i = (Fin.natAdd 464 (Fin.castAdd 128 (⟨i.val-464, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_464 _
  by_cases h480 : i.val < 496
  · have he : i = (Fin.natAdd 480 (Fin.castAdd 112 (⟨i.val-480, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_480 _
  by_cases h496 : i.val < 512
  · have he : i = (Fin.natAdd 496 (Fin.castAdd 96 (⟨i.val-496, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_496 _
  by_cases h512 : i.val < 528
  · have he : i = (Fin.natAdd 512 (Fin.castAdd 80 (⟨i.val-512, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_512 _
  by_cases h528 : i.val < 544
  · have he : i = (Fin.natAdd 528 (Fin.castAdd 64 (⟨i.val-528, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_528 _
  by_cases h544 : i.val < 560
  · have he : i = (Fin.natAdd 544 (Fin.castAdd 48 (⟨i.val-544, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_544 _
  by_cases h560 : i.val < 576
  · have he : i = (Fin.natAdd 560 (Fin.castAdd 32 (⟨i.val-560, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_560 _
  by_cases h576 : i.val < 592
  · have he : i = (Fin.natAdd 576 (Fin.castAdd 16 (⟨i.val-576, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward2_576 _
  have he : i = (Fin.natAdd 592 (Fin.castAdd 0 (⟨i.val-592, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact forward2_592 _

theorem step2_forward (i : Fin 608) : step2Rows.get i =
    combine layer3Rows (forward2.get i) := by
  simpa only [forward2Pred] using forward2_all i

private def reverse2Pred (i : Fin 32) : Prop :=
  layer3Rows.get i = sparseCombine step2Rows (reverse2Sparse.get i)

attribute [local irreducible] reverse2Pred

private theorem reverse2_0 (i : Fin 16) :
    reverse2Pred (Fin.natAdd 0 (Fin.castAdd 16 i)) := by
  unfold reverse2Pred
  rw [reverse2Sparse_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step2Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse2_16 (i : Fin 16) :
    reverse2Pred (Fin.natAdd 16 (Fin.castAdd 0 i)) := by
  unfold reverse2Pred
  rw [reverse2Sparse_chunk1 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step2Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse2_all (i : Fin 32) : reverse2Pred i := by
  by_cases h0 : i.val < 16
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 16 (⟨i.val-0, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse2_0 _
  have he : i = (Fin.natAdd 16 (Fin.castAdd 0 (⟨i.val-16, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact reverse2_16 _

theorem step2_reverse (i : Fin 32) : layer3Rows.get i =
    sparseCombine step2Rows (reverse2Sparse.get i) := by
  simpa only [reverse2Pred] using reverse2_all i

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
