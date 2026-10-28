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
private def source1_0Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 0) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(0 : Fin 8)))

attribute [local irreducible] source1_0Pred

private theorem source1_0_0 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 0+8*(0+i.val); omega) (by change 0+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_8 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 0+8*(8+i.val); omega) (by change 0+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_16 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 0+8*(16+i.val); omega) (by change 0+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_24 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 0+8*(24+i.val); omega) (by change 0+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_32 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 0+8*(32+i.val); omega) (by change 0+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_40 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 0+8*(40+i.val); omega) (by change 0+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_48 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 0+8*(48+i.val); omega) (by change 0+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_56 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 0+8*(56+i.val); omega) (by change 0+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_64 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 0+8*(64+i.val); omega) (by change 0+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_72 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 0+8*(72+i.val); omega) (by change 0+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_80 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 0+8*(80+i.val); omega) (by change 0+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_88 (i : Fin 8) :
    source1_0Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 0+8*(88+i.val); omega) (by change 0+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_96 (i : Fin 5) :
    source1_0Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_0Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 0+8*(96+i.val); omega) (by change 0+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_0_all (i : Fin 101) : source1_0Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_0_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_0_96 _

private def source1_1Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 1) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(1 : Fin 8)))

attribute [local irreducible] source1_1Pred

private theorem source1_1_0 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 1+8*(0+i.val); omega) (by change 1+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_8 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 1+8*(8+i.val); omega) (by change 1+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_16 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 1+8*(16+i.val); omega) (by change 1+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_24 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 1+8*(24+i.val); omega) (by change 1+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_32 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 1+8*(32+i.val); omega) (by change 1+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_40 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 1+8*(40+i.val); omega) (by change 1+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_48 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 1+8*(48+i.val); omega) (by change 1+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_56 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 1+8*(56+i.val); omega) (by change 1+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_64 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 1+8*(64+i.val); omega) (by change 1+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_72 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 1+8*(72+i.val); omega) (by change 1+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_80 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 1+8*(80+i.val); omega) (by change 1+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_88 (i : Fin 8) :
    source1_1Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 1+8*(88+i.val); omega) (by change 1+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_96 (i : Fin 5) :
    source1_1Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_1Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 1+8*(96+i.val); omega) (by change 1+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_1_all (i : Fin 101) : source1_1Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_1_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_1_96 _

private def source1_2Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 2) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(2 : Fin 8)))

attribute [local irreducible] source1_2Pred

private theorem source1_2_0 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 2+8*(0+i.val); omega) (by change 2+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_8 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 2+8*(8+i.val); omega) (by change 2+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_16 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 2+8*(16+i.val); omega) (by change 2+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_24 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 2+8*(24+i.val); omega) (by change 2+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_32 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 2+8*(32+i.val); omega) (by change 2+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_40 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 2+8*(40+i.val); omega) (by change 2+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_48 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 2+8*(48+i.val); omega) (by change 2+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_56 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 2+8*(56+i.val); omega) (by change 2+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_64 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 2+8*(64+i.val); omega) (by change 2+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_72 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 2+8*(72+i.val); omega) (by change 2+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_80 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 2+8*(80+i.val); omega) (by change 2+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_88 (i : Fin 8) :
    source1_2Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 2+8*(88+i.val); omega) (by change 2+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_96 (i : Fin 5) :
    source1_2Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_2Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 2+8*(96+i.val); omega) (by change 2+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_2_all (i : Fin 101) : source1_2Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_2_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_2_96 _

private def source1_3Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 3) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(3 : Fin 8)))

attribute [local irreducible] source1_3Pred

private theorem source1_3_0 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 3+8*(0+i.val); omega) (by change 3+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_8 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 3+8*(8+i.val); omega) (by change 3+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_16 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 3+8*(16+i.val); omega) (by change 3+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_24 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 3+8*(24+i.val); omega) (by change 3+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_32 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 3+8*(32+i.val); omega) (by change 3+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_40 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 3+8*(40+i.val); omega) (by change 3+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_48 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 3+8*(48+i.val); omega) (by change 3+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_56 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 3+8*(56+i.val); omega) (by change 3+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_64 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 3+8*(64+i.val); omega) (by change 3+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_72 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 3+8*(72+i.val); omega) (by change 3+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_80 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 3+8*(80+i.val); omega) (by change 3+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_88 (i : Fin 8) :
    source1_3Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 3+8*(88+i.val); omega) (by change 3+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_96 (i : Fin 5) :
    source1_3Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_3Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 3+8*(96+i.val); omega) (by change 3+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_3_all (i : Fin 101) : source1_3Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_3_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_3_96 _

private def source1_4Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 4) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(4 : Fin 8)))

attribute [local irreducible] source1_4Pred

private theorem source1_4_0 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 4+8*(0+i.val); omega) (by change 4+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_8 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 4+8*(8+i.val); omega) (by change 4+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_16 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 4+8*(16+i.val); omega) (by change 4+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_24 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 4+8*(24+i.val); omega) (by change 4+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_32 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 4+8*(32+i.val); omega) (by change 4+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_40 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 4+8*(40+i.val); omega) (by change 4+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_48 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 4+8*(48+i.val); omega) (by change 4+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_56 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 4+8*(56+i.val); omega) (by change 4+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_64 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 4+8*(64+i.val); omega) (by change 4+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_72 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 4+8*(72+i.val); omega) (by change 4+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_80 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 4+8*(80+i.val); omega) (by change 4+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_88 (i : Fin 8) :
    source1_4Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 4+8*(88+i.val); omega) (by change 4+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_96 (i : Fin 5) :
    source1_4Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_4Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 4+8*(96+i.val); omega) (by change 4+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_4_all (i : Fin 101) : source1_4Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_4_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_4_96 _

private def source1_5Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 5) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(5 : Fin 8)))

attribute [local irreducible] source1_5Pred

private theorem source1_5_0 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 5+8*(0+i.val); omega) (by change 5+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_8 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 5+8*(8+i.val); omega) (by change 5+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_16 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 5+8*(16+i.val); omega) (by change 5+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_24 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 5+8*(24+i.val); omega) (by change 5+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_32 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 5+8*(32+i.val); omega) (by change 5+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_40 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 5+8*(40+i.val); omega) (by change 5+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_48 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 5+8*(48+i.val); omega) (by change 5+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_56 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 5+8*(56+i.val); omega) (by change 5+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_64 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 5+8*(64+i.val); omega) (by change 5+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_72 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 5+8*(72+i.val); omega) (by change 5+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_80 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 5+8*(80+i.val); omega) (by change 5+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_88 (i : Fin 8) :
    source1_5Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 5+8*(88+i.val); omega) (by change 5+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_96 (i : Fin 5) :
    source1_5Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_5Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 5+8*(96+i.val); omega) (by change 5+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_5_all (i : Fin 101) : source1_5Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_5_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_5_96 _

private def source1_6Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 6) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(6 : Fin 8)))

attribute [local irreducible] source1_6Pred

private theorem source1_6_0 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 6+8*(0+i.val); omega) (by change 6+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_8 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 6+8*(8+i.val); omega) (by change 6+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_16 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 6+8*(16+i.val); omega) (by change 6+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_24 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 6+8*(24+i.val); omega) (by change 6+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_32 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 6+8*(32+i.val); omega) (by change 6+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_40 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 6+8*(40+i.val); omega) (by change 6+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_48 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 6+8*(48+i.val); omega) (by change 6+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_56 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 6+8*(56+i.val); omega) (by change 6+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_64 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 6+8*(64+i.val); omega) (by change 6+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_72 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 6+8*(72+i.val); omega) (by change 6+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_80 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 6+8*(80+i.val); omega) (by change 6+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_88 (i : Fin 8) :
    source1_6Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 6+8*(88+i.val); omega) (by change 6+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_96 (i : Fin 5) :
    source1_6Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_6Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 6+8*(96+i.val); omega) (by change 6+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_6_all (i : Fin 101) : source1_6Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_6_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_6_96 _

private def source1_7Pred (i : Fin 101) : Prop :=
  packedRow (layer1Rows.get i) (generatorRows 7) ^^^ layer1Rows.get i = step1Rows.get (finProdFinEquiv (i,(7 : Fin 8)))

attribute [local irreducible] source1_7Pred

private theorem source1_7_0 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 0 (Fin.castAdd 93 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 7+8*(0+i.val); omega) (by change 7+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_8 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 8 (Fin.castAdd 85 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 7+8*(8+i.val); omega) (by change 7+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_16 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 16 (Fin.castAdd 77 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 7+8*(16+i.val); omega) (by change 7+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_24 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 24 (Fin.castAdd 69 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 7+8*(24+i.val); omega) (by change 7+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_32 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 32 (Fin.castAdd 61 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 7+8*(32+i.val); omega) (by change 7+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_40 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 40 (Fin.castAdd 53 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 7+8*(40+i.val); omega) (by change 7+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_48 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 48 (Fin.castAdd 45 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 7+8*(48+i.val); omega) (by change 7+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_56 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 56 (Fin.castAdd 37 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 7+8*(56+i.val); omega) (by change 7+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_64 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 64 (Fin.castAdd 29 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 7+8*(64+i.val); omega) (by change 7+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_72 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 72 (Fin.castAdd 21 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 7+8*(72+i.val); omega) (by change 7+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_80 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 80 (Fin.castAdd 13 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 7+8*(80+i.val); omega) (by change 7+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_88 (i : Fin 8) :
    source1_7Pred (Fin.natAdd 88 (Fin.castAdd 5 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 7+8*(88+i.val); omega) (by change 7+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_96 (i : Fin 5) :
    source1_7Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold source1_7Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 7+8*(96+i.val); omega) (by change 7+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source1_7_all (i : Fin 101) : source1_7Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 93 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 85 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 77 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 69 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 61 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 53 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 45 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 37 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 29 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 21 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 13 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 5 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source1_7_88 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source1_7_96 _

theorem step1_source (i : Fin 101) (j : Fin 8) :
    packedRow (layer1Rows.get i) (generatorRows j) ^^^ layer1Rows.get i =
      step1Rows.get (finProdFinEquiv (i,j)) := by
  have hj : ∀ j : Fin 8, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by decide +kernel
  rcases hj j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [source1_0Pred] using source1_0_all i
  · simpa only [source1_1Pred] using source1_1_all i
  · simpa only [source1_2Pred] using source1_2_all i
  · simpa only [source1_3Pred] using source1_3_all i
  · simpa only [source1_4Pred] using source1_4_all i
  · simpa only [source1_5Pred] using source1_5_all i
  · simpa only [source1_6Pred] using source1_6_all i
  · simpa only [source1_7Pred] using source1_7_all i

private def forward1Pred (i : Fin 808) : Prop :=
  step1Rows.get i = combine layer2Rows (forward1.get i)

attribute [local irreducible] forward1Pred

private theorem forward1_0 (i : Fin 16) :
    forward1Pred (Fin.natAdd 0 (Fin.castAdd 792 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  rw [forward1_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_16 (i : Fin 16) :
    forward1Pred (Fin.natAdd 16 (Fin.castAdd 776 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  rw [forward1_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_32 (i : Fin 16) :
    forward1Pred (Fin.natAdd 32 (Fin.castAdd 760 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  rw [forward1_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_48 (i : Fin 16) :
    forward1Pred (Fin.natAdd 48 (Fin.castAdd 744 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  rw [forward1_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_64 (i : Fin 16) :
    forward1Pred (Fin.natAdd 64 (Fin.castAdd 728 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  rw [forward1_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_80 (i : Fin 16) :
    forward1Pred (Fin.natAdd 80 (Fin.castAdd 712 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  rw [forward1_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_96 (i : Fin 16) :
    forward1Pred (Fin.natAdd 96 (Fin.castAdd 696 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  rw [forward1_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_112 (i : Fin 16) :
    forward1Pred (Fin.natAdd 112 (Fin.castAdd 680 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  rw [forward1_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_128 (i : Fin 16) :
    forward1Pred (Fin.natAdd 128 (Fin.castAdd 664 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  rw [forward1_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_144 (i : Fin 16) :
    forward1Pred (Fin.natAdd 144 (Fin.castAdd 648 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  rw [forward1_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_160 (i : Fin 16) :
    forward1Pred (Fin.natAdd 160 (Fin.castAdd 632 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  rw [forward1_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_176 (i : Fin 16) :
    forward1Pred (Fin.natAdd 176 (Fin.castAdd 616 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  rw [forward1_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_192 (i : Fin 16) :
    forward1Pred (Fin.natAdd 192 (Fin.castAdd 600 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  rw [forward1_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_208 (i : Fin 16) :
    forward1Pred (Fin.natAdd 208 (Fin.castAdd 584 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  rw [forward1_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_224 (i : Fin 16) :
    forward1Pred (Fin.natAdd 224 (Fin.castAdd 568 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  rw [forward1_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_240 (i : Fin 16) :
    forward1Pred (Fin.natAdd 240 (Fin.castAdd 552 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  rw [forward1_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_256 (i : Fin 16) :
    forward1Pred (Fin.natAdd 256 (Fin.castAdd 536 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 256+i.val; omega) (by change 256+i.val < _; omega)]
  rw [forward1_chunk4 _ (by change _ ≤ 256+i.val; omega) (by change 256+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_272 (i : Fin 16) :
    forward1Pred (Fin.natAdd 272 (Fin.castAdd 520 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 272+i.val; omega) (by change 272+i.val < _; omega)]
  rw [forward1_chunk4 _ (by change _ ≤ 272+i.val; omega) (by change 272+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_288 (i : Fin 16) :
    forward1Pred (Fin.natAdd 288 (Fin.castAdd 504 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 288+i.val; omega) (by change 288+i.val < _; omega)]
  rw [forward1_chunk4 _ (by change _ ≤ 288+i.val; omega) (by change 288+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_304 (i : Fin 16) :
    forward1Pred (Fin.natAdd 304 (Fin.castAdd 488 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk4 _ (by change _ ≤ 304+i.val; omega) (by change 304+i.val < _; omega)]
  rw [forward1_chunk4 _ (by change _ ≤ 304+i.val; omega) (by change 304+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_320 (i : Fin 16) :
    forward1Pred (Fin.natAdd 320 (Fin.castAdd 472 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 320+i.val; omega) (by change 320+i.val < _; omega)]
  rw [forward1_chunk5 _ (by change _ ≤ 320+i.val; omega) (by change 320+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_336 (i : Fin 16) :
    forward1Pred (Fin.natAdd 336 (Fin.castAdd 456 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 336+i.val; omega) (by change 336+i.val < _; omega)]
  rw [forward1_chunk5 _ (by change _ ≤ 336+i.val; omega) (by change 336+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_352 (i : Fin 16) :
    forward1Pred (Fin.natAdd 352 (Fin.castAdd 440 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 352+i.val; omega) (by change 352+i.val < _; omega)]
  rw [forward1_chunk5 _ (by change _ ≤ 352+i.val; omega) (by change 352+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_368 (i : Fin 16) :
    forward1Pred (Fin.natAdd 368 (Fin.castAdd 424 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk5 _ (by change _ ≤ 368+i.val; omega) (by change 368+i.val < _; omega)]
  rw [forward1_chunk5 _ (by change _ ≤ 368+i.val; omega) (by change 368+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_384 (i : Fin 16) :
    forward1Pred (Fin.natAdd 384 (Fin.castAdd 408 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 384+i.val; omega) (by change 384+i.val < _; omega)]
  rw [forward1_chunk6 _ (by change _ ≤ 384+i.val; omega) (by change 384+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_400 (i : Fin 16) :
    forward1Pred (Fin.natAdd 400 (Fin.castAdd 392 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 400+i.val; omega) (by change 400+i.val < _; omega)]
  rw [forward1_chunk6 _ (by change _ ≤ 400+i.val; omega) (by change 400+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_416 (i : Fin 16) :
    forward1Pred (Fin.natAdd 416 (Fin.castAdd 376 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 416+i.val; omega) (by change 416+i.val < _; omega)]
  rw [forward1_chunk6 _ (by change _ ≤ 416+i.val; omega) (by change 416+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_432 (i : Fin 16) :
    forward1Pred (Fin.natAdd 432 (Fin.castAdd 360 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk6 _ (by change _ ≤ 432+i.val; omega) (by change 432+i.val < _; omega)]
  rw [forward1_chunk6 _ (by change _ ≤ 432+i.val; omega) (by change 432+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_448 (i : Fin 16) :
    forward1Pred (Fin.natAdd 448 (Fin.castAdd 344 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 448+i.val; omega) (by change 448+i.val < _; omega)]
  rw [forward1_chunk7 _ (by change _ ≤ 448+i.val; omega) (by change 448+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_464 (i : Fin 16) :
    forward1Pred (Fin.natAdd 464 (Fin.castAdd 328 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 464+i.val; omega) (by change 464+i.val < _; omega)]
  rw [forward1_chunk7 _ (by change _ ≤ 464+i.val; omega) (by change 464+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_480 (i : Fin 16) :
    forward1Pred (Fin.natAdd 480 (Fin.castAdd 312 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 480+i.val; omega) (by change 480+i.val < _; omega)]
  rw [forward1_chunk7 _ (by change _ ≤ 480+i.val; omega) (by change 480+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_496 (i : Fin 16) :
    forward1Pred (Fin.natAdd 496 (Fin.castAdd 296 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk7 _ (by change _ ≤ 496+i.val; omega) (by change 496+i.val < _; omega)]
  rw [forward1_chunk7 _ (by change _ ≤ 496+i.val; omega) (by change 496+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_512 (i : Fin 16) :
    forward1Pred (Fin.natAdd 512 (Fin.castAdd 280 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 512+i.val; omega) (by change 512+i.val < _; omega)]
  rw [forward1_chunk8 _ (by change _ ≤ 512+i.val; omega) (by change 512+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_528 (i : Fin 16) :
    forward1Pred (Fin.natAdd 528 (Fin.castAdd 264 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 528+i.val; omega) (by change 528+i.val < _; omega)]
  rw [forward1_chunk8 _ (by change _ ≤ 528+i.val; omega) (by change 528+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_544 (i : Fin 16) :
    forward1Pred (Fin.natAdd 544 (Fin.castAdd 248 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 544+i.val; omega) (by change 544+i.val < _; omega)]
  rw [forward1_chunk8 _ (by change _ ≤ 544+i.val; omega) (by change 544+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_560 (i : Fin 16) :
    forward1Pred (Fin.natAdd 560 (Fin.castAdd 232 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk8 _ (by change _ ≤ 560+i.val; omega) (by change 560+i.val < _; omega)]
  rw [forward1_chunk8 _ (by change _ ≤ 560+i.val; omega) (by change 560+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_576 (i : Fin 16) :
    forward1Pred (Fin.natAdd 576 (Fin.castAdd 216 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 576+i.val; omega) (by change 576+i.val < _; omega)]
  rw [forward1_chunk9 _ (by change _ ≤ 576+i.val; omega) (by change 576+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_592 (i : Fin 16) :
    forward1Pred (Fin.natAdd 592 (Fin.castAdd 200 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 592+i.val; omega) (by change 592+i.val < _; omega)]
  rw [forward1_chunk9 _ (by change _ ≤ 592+i.val; omega) (by change 592+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_608 (i : Fin 16) :
    forward1Pred (Fin.natAdd 608 (Fin.castAdd 184 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 608+i.val; omega) (by change 608+i.val < _; omega)]
  rw [forward1_chunk9 _ (by change _ ≤ 608+i.val; omega) (by change 608+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_624 (i : Fin 16) :
    forward1Pred (Fin.natAdd 624 (Fin.castAdd 168 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk9 _ (by change _ ≤ 624+i.val; omega) (by change 624+i.val < _; omega)]
  rw [forward1_chunk9 _ (by change _ ≤ 624+i.val; omega) (by change 624+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_640 (i : Fin 16) :
    forward1Pred (Fin.natAdd 640 (Fin.castAdd 152 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 640+i.val; omega) (by change 640+i.val < _; omega)]
  rw [forward1_chunk10 _ (by change _ ≤ 640+i.val; omega) (by change 640+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_656 (i : Fin 16) :
    forward1Pred (Fin.natAdd 656 (Fin.castAdd 136 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 656+i.val; omega) (by change 656+i.val < _; omega)]
  rw [forward1_chunk10 _ (by change _ ≤ 656+i.val; omega) (by change 656+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_672 (i : Fin 16) :
    forward1Pred (Fin.natAdd 672 (Fin.castAdd 120 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 672+i.val; omega) (by change 672+i.val < _; omega)]
  rw [forward1_chunk10 _ (by change _ ≤ 672+i.val; omega) (by change 672+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_688 (i : Fin 16) :
    forward1Pred (Fin.natAdd 688 (Fin.castAdd 104 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk10 _ (by change _ ≤ 688+i.val; omega) (by change 688+i.val < _; omega)]
  rw [forward1_chunk10 _ (by change _ ≤ 688+i.val; omega) (by change 688+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_704 (i : Fin 16) :
    forward1Pred (Fin.natAdd 704 (Fin.castAdd 88 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 704+i.val; omega) (by change 704+i.val < _; omega)]
  rw [forward1_chunk11 _ (by change _ ≤ 704+i.val; omega) (by change 704+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_720 (i : Fin 16) :
    forward1Pred (Fin.natAdd 720 (Fin.castAdd 72 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 720+i.val; omega) (by change 720+i.val < _; omega)]
  rw [forward1_chunk11 _ (by change _ ≤ 720+i.val; omega) (by change 720+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_736 (i : Fin 16) :
    forward1Pred (Fin.natAdd 736 (Fin.castAdd 56 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 736+i.val; omega) (by change 736+i.val < _; omega)]
  rw [forward1_chunk11 _ (by change _ ≤ 736+i.val; omega) (by change 736+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_752 (i : Fin 16) :
    forward1Pred (Fin.natAdd 752 (Fin.castAdd 40 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk11 _ (by change _ ≤ 752+i.val; omega) (by change 752+i.val < _; omega)]
  rw [forward1_chunk11 _ (by change _ ≤ 752+i.val; omega) (by change 752+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_768 (i : Fin 16) :
    forward1Pred (Fin.natAdd 768 (Fin.castAdd 24 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 768+i.val; omega) (by change 768+i.val < _; omega)]
  rw [forward1_chunk12 _ (by change _ ≤ 768+i.val; omega) (by change 768+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_784 (i : Fin 16) :
    forward1Pred (Fin.natAdd 784 (Fin.castAdd 8 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 784+i.val; omega) (by change 784+i.val < _; omega)]
  rw [forward1_chunk12 _ (by change _ ≤ 784+i.val; omega) (by change 784+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_800 (i : Fin 8) :
    forward1Pred (Fin.natAdd 800 (Fin.castAdd 0 i)) := by
  unfold forward1Pred
  rw [step1Rows_chunk12 _ (by change _ ≤ 800+i.val; omega) (by change 800+i.val < _; omega)]
  rw [forward1_chunk12 _ (by change _ ≤ 800+i.val; omega) (by change 800+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward1_all (i : Fin 808) : forward1Pred i := by
  by_cases h0 : i.val < 16
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 792 (⟨i.val-0, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_0 _
  by_cases h16 : i.val < 32
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 776 (⟨i.val-16, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_16 _
  by_cases h32 : i.val < 48
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 760 (⟨i.val-32, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_32 _
  by_cases h48 : i.val < 64
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 744 (⟨i.val-48, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_48 _
  by_cases h64 : i.val < 80
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 728 (⟨i.val-64, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_64 _
  by_cases h80 : i.val < 96
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 712 (⟨i.val-80, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_80 _
  by_cases h96 : i.val < 112
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 696 (⟨i.val-96, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_96 _
  by_cases h112 : i.val < 128
  · have he : i = (Fin.natAdd 112 (Fin.castAdd 680 (⟨i.val-112, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_112 _
  by_cases h128 : i.val < 144
  · have he : i = (Fin.natAdd 128 (Fin.castAdd 664 (⟨i.val-128, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_128 _
  by_cases h144 : i.val < 160
  · have he : i = (Fin.natAdd 144 (Fin.castAdd 648 (⟨i.val-144, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_144 _
  by_cases h160 : i.val < 176
  · have he : i = (Fin.natAdd 160 (Fin.castAdd 632 (⟨i.val-160, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_160 _
  by_cases h176 : i.val < 192
  · have he : i = (Fin.natAdd 176 (Fin.castAdd 616 (⟨i.val-176, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_176 _
  by_cases h192 : i.val < 208
  · have he : i = (Fin.natAdd 192 (Fin.castAdd 600 (⟨i.val-192, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_192 _
  by_cases h208 : i.val < 224
  · have he : i = (Fin.natAdd 208 (Fin.castAdd 584 (⟨i.val-208, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_208 _
  by_cases h224 : i.val < 240
  · have he : i = (Fin.natAdd 224 (Fin.castAdd 568 (⟨i.val-224, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_224 _
  by_cases h240 : i.val < 256
  · have he : i = (Fin.natAdd 240 (Fin.castAdd 552 (⟨i.val-240, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_240 _
  by_cases h256 : i.val < 272
  · have he : i = (Fin.natAdd 256 (Fin.castAdd 536 (⟨i.val-256, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_256 _
  by_cases h272 : i.val < 288
  · have he : i = (Fin.natAdd 272 (Fin.castAdd 520 (⟨i.val-272, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_272 _
  by_cases h288 : i.val < 304
  · have he : i = (Fin.natAdd 288 (Fin.castAdd 504 (⟨i.val-288, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_288 _
  by_cases h304 : i.val < 320
  · have he : i = (Fin.natAdd 304 (Fin.castAdd 488 (⟨i.val-304, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_304 _
  by_cases h320 : i.val < 336
  · have he : i = (Fin.natAdd 320 (Fin.castAdd 472 (⟨i.val-320, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_320 _
  by_cases h336 : i.val < 352
  · have he : i = (Fin.natAdd 336 (Fin.castAdd 456 (⟨i.val-336, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_336 _
  by_cases h352 : i.val < 368
  · have he : i = (Fin.natAdd 352 (Fin.castAdd 440 (⟨i.val-352, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_352 _
  by_cases h368 : i.val < 384
  · have he : i = (Fin.natAdd 368 (Fin.castAdd 424 (⟨i.val-368, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_368 _
  by_cases h384 : i.val < 400
  · have he : i = (Fin.natAdd 384 (Fin.castAdd 408 (⟨i.val-384, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_384 _
  by_cases h400 : i.val < 416
  · have he : i = (Fin.natAdd 400 (Fin.castAdd 392 (⟨i.val-400, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_400 _
  by_cases h416 : i.val < 432
  · have he : i = (Fin.natAdd 416 (Fin.castAdd 376 (⟨i.val-416, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_416 _
  by_cases h432 : i.val < 448
  · have he : i = (Fin.natAdd 432 (Fin.castAdd 360 (⟨i.val-432, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_432 _
  by_cases h448 : i.val < 464
  · have he : i = (Fin.natAdd 448 (Fin.castAdd 344 (⟨i.val-448, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_448 _
  by_cases h464 : i.val < 480
  · have he : i = (Fin.natAdd 464 (Fin.castAdd 328 (⟨i.val-464, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_464 _
  by_cases h480 : i.val < 496
  · have he : i = (Fin.natAdd 480 (Fin.castAdd 312 (⟨i.val-480, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_480 _
  by_cases h496 : i.val < 512
  · have he : i = (Fin.natAdd 496 (Fin.castAdd 296 (⟨i.val-496, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_496 _
  by_cases h512 : i.val < 528
  · have he : i = (Fin.natAdd 512 (Fin.castAdd 280 (⟨i.val-512, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_512 _
  by_cases h528 : i.val < 544
  · have he : i = (Fin.natAdd 528 (Fin.castAdd 264 (⟨i.val-528, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_528 _
  by_cases h544 : i.val < 560
  · have he : i = (Fin.natAdd 544 (Fin.castAdd 248 (⟨i.val-544, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_544 _
  by_cases h560 : i.val < 576
  · have he : i = (Fin.natAdd 560 (Fin.castAdd 232 (⟨i.val-560, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_560 _
  by_cases h576 : i.val < 592
  · have he : i = (Fin.natAdd 576 (Fin.castAdd 216 (⟨i.val-576, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_576 _
  by_cases h592 : i.val < 608
  · have he : i = (Fin.natAdd 592 (Fin.castAdd 200 (⟨i.val-592, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_592 _
  by_cases h608 : i.val < 624
  · have he : i = (Fin.natAdd 608 (Fin.castAdd 184 (⟨i.val-608, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_608 _
  by_cases h624 : i.val < 640
  · have he : i = (Fin.natAdd 624 (Fin.castAdd 168 (⟨i.val-624, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_624 _
  by_cases h640 : i.val < 656
  · have he : i = (Fin.natAdd 640 (Fin.castAdd 152 (⟨i.val-640, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_640 _
  by_cases h656 : i.val < 672
  · have he : i = (Fin.natAdd 656 (Fin.castAdd 136 (⟨i.val-656, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_656 _
  by_cases h672 : i.val < 688
  · have he : i = (Fin.natAdd 672 (Fin.castAdd 120 (⟨i.val-672, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_672 _
  by_cases h688 : i.val < 704
  · have he : i = (Fin.natAdd 688 (Fin.castAdd 104 (⟨i.val-688, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_688 _
  by_cases h704 : i.val < 720
  · have he : i = (Fin.natAdd 704 (Fin.castAdd 88 (⟨i.val-704, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_704 _
  by_cases h720 : i.val < 736
  · have he : i = (Fin.natAdd 720 (Fin.castAdd 72 (⟨i.val-720, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_720 _
  by_cases h736 : i.val < 752
  · have he : i = (Fin.natAdd 736 (Fin.castAdd 56 (⟨i.val-736, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_736 _
  by_cases h752 : i.val < 768
  · have he : i = (Fin.natAdd 752 (Fin.castAdd 40 (⟨i.val-752, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_752 _
  by_cases h768 : i.val < 784
  · have he : i = (Fin.natAdd 768 (Fin.castAdd 24 (⟨i.val-768, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_768 _
  by_cases h784 : i.val < 800
  · have he : i = (Fin.natAdd 784 (Fin.castAdd 8 (⟨i.val-784, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward1_784 _
  have he : i = (Fin.natAdd 800 (Fin.castAdd 0 (⟨i.val-800, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact forward1_800 _

theorem step1_forward (i : Fin 808) : step1Rows.get i =
    combine layer2Rows (forward1.get i) := by
  simpa only [forward1Pred] using forward1_all i

private def reverse1Pred (i : Fin 76) : Prop :=
  layer2Rows.get i = sparseCombine step1Rows (reverse1Sparse.get i)

attribute [local irreducible] reverse1Pred

private theorem reverse1_0 (i : Fin 16) :
    reverse1Pred (Fin.natAdd 0 (Fin.castAdd 60 i)) := by
  unfold reverse1Pred
  rw [reverse1Sparse_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step1Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse1_16 (i : Fin 16) :
    reverse1Pred (Fin.natAdd 16 (Fin.castAdd 44 i)) := by
  unfold reverse1Pred
  rw [reverse1Sparse_chunk1 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step1Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse1_32 (i : Fin 16) :
    reverse1Pred (Fin.natAdd 32 (Fin.castAdd 28 i)) := by
  unfold reverse1Pred
  rw [reverse1Sparse_chunk2 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step1Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse1_48 (i : Fin 16) :
    reverse1Pred (Fin.natAdd 48 (Fin.castAdd 12 i)) := by
  unfold reverse1Pred
  rw [reverse1Sparse_chunk3 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step1Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse1_64 (i : Fin 12) :
    reverse1Pred (Fin.natAdd 64 (Fin.castAdd 0 i)) := by
  unfold reverse1Pred
  rw [reverse1Sparse_chunk4 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step1Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse1_all (i : Fin 76) : reverse1Pred i := by
  by_cases h0 : i.val < 16
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 60 (⟨i.val-0, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse1_0 _
  by_cases h16 : i.val < 32
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 44 (⟨i.val-16, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse1_16 _
  by_cases h32 : i.val < 48
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 28 (⟨i.val-32, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse1_32 _
  by_cases h48 : i.val < 64
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 12 (⟨i.val-48, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse1_48 _
  have he : i = (Fin.natAdd 64 (Fin.castAdd 0 (⟨i.val-64, by omega⟩ : Fin 12))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact reverse1_64 _

theorem step1_reverse (i : Fin 76) : layer2Rows.get i =
    sparseCombine step1Rows (reverse1Sparse.get i) := by
  simpa only [reverse1Pred] using reverse1_all i

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
