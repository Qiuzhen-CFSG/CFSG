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
private def source0_0Pred (i : Fin 112) : Prop :=
  (generatorRows 0).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(0 : Fin 8)))

attribute [local irreducible] source0_0Pred

private theorem source0_0_0 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 0+8*(0+i.val); omega) (by change 0+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_8 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 0+8*(8+i.val); omega) (by change 0+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_16 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 0+8*(16+i.val); omega) (by change 0+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_24 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 0+8*(24+i.val); omega) (by change 0+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_32 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 0+8*(32+i.val); omega) (by change 0+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_40 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 0+8*(40+i.val); omega) (by change 0+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_48 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 0+8*(48+i.val); omega) (by change 0+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_56 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 0+8*(56+i.val); omega) (by change 0+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_64 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 0+8*(64+i.val); omega) (by change 0+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_72 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 0+8*(72+i.val); omega) (by change 0+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_80 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 0+8*(80+i.val); omega) (by change 0+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_88 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 0+8*(88+i.val); omega) (by change 0+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_96 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 0+8*(96+i.val); omega) (by change 0+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_104 (i : Fin 8) :
    source0_0Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_0Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 0+8*(104+i.val); omega) (by change 0+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_0_all (i : Fin 112) : source0_0Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_0_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_0_104 _

private def source0_1Pred (i : Fin 112) : Prop :=
  (generatorRows 1).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(1 : Fin 8)))

attribute [local irreducible] source0_1Pred

private theorem source0_1_0 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 1+8*(0+i.val); omega) (by change 1+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_8 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 1+8*(8+i.val); omega) (by change 1+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_16 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 1+8*(16+i.val); omega) (by change 1+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_24 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 1+8*(24+i.val); omega) (by change 1+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_32 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 1+8*(32+i.val); omega) (by change 1+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_40 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 1+8*(40+i.val); omega) (by change 1+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_48 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 1+8*(48+i.val); omega) (by change 1+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_56 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 1+8*(56+i.val); omega) (by change 1+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_64 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 1+8*(64+i.val); omega) (by change 1+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_72 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 1+8*(72+i.val); omega) (by change 1+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_80 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 1+8*(80+i.val); omega) (by change 1+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_88 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 1+8*(88+i.val); omega) (by change 1+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_96 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 1+8*(96+i.val); omega) (by change 1+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_104 (i : Fin 8) :
    source0_1Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_1Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 1+8*(104+i.val); omega) (by change 1+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_1_all (i : Fin 112) : source0_1Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_1_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_1_104 _

private def source0_2Pred (i : Fin 112) : Prop :=
  (generatorRows 2).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(2 : Fin 8)))

attribute [local irreducible] source0_2Pred

private theorem source0_2_0 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 2+8*(0+i.val); omega) (by change 2+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_8 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 2+8*(8+i.val); omega) (by change 2+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_16 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 2+8*(16+i.val); omega) (by change 2+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_24 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 2+8*(24+i.val); omega) (by change 2+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_32 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 2+8*(32+i.val); omega) (by change 2+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_40 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 2+8*(40+i.val); omega) (by change 2+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_48 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 2+8*(48+i.val); omega) (by change 2+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_56 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 2+8*(56+i.val); omega) (by change 2+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_64 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 2+8*(64+i.val); omega) (by change 2+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_72 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 2+8*(72+i.val); omega) (by change 2+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_80 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 2+8*(80+i.val); omega) (by change 2+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_88 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 2+8*(88+i.val); omega) (by change 2+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_96 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 2+8*(96+i.val); omega) (by change 2+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_104 (i : Fin 8) :
    source0_2Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_2Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 2+8*(104+i.val); omega) (by change 2+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_2_all (i : Fin 112) : source0_2Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_2_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_2_104 _

private def source0_3Pred (i : Fin 112) : Prop :=
  (generatorRows 3).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(3 : Fin 8)))

attribute [local irreducible] source0_3Pred

private theorem source0_3_0 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 3+8*(0+i.val); omega) (by change 3+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_8 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 3+8*(8+i.val); omega) (by change 3+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_16 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 3+8*(16+i.val); omega) (by change 3+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_24 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 3+8*(24+i.val); omega) (by change 3+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_32 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 3+8*(32+i.val); omega) (by change 3+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_40 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 3+8*(40+i.val); omega) (by change 3+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_48 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 3+8*(48+i.val); omega) (by change 3+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_56 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 3+8*(56+i.val); omega) (by change 3+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_64 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 3+8*(64+i.val); omega) (by change 3+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_72 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 3+8*(72+i.val); omega) (by change 3+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_80 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 3+8*(80+i.val); omega) (by change 3+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_88 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 3+8*(88+i.val); omega) (by change 3+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_96 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 3+8*(96+i.val); omega) (by change 3+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_104 (i : Fin 8) :
    source0_3Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_3Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 3+8*(104+i.val); omega) (by change 3+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_3_all (i : Fin 112) : source0_3Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_3_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_3_104 _

private def source0_4Pred (i : Fin 112) : Prop :=
  (generatorRows 4).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(4 : Fin 8)))

attribute [local irreducible] source0_4Pred

private theorem source0_4_0 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 4+8*(0+i.val); omega) (by change 4+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_8 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 4+8*(8+i.val); omega) (by change 4+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_16 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 4+8*(16+i.val); omega) (by change 4+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_24 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 4+8*(24+i.val); omega) (by change 4+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_32 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 4+8*(32+i.val); omega) (by change 4+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_40 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 4+8*(40+i.val); omega) (by change 4+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_48 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 4+8*(48+i.val); omega) (by change 4+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_56 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 4+8*(56+i.val); omega) (by change 4+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_64 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 4+8*(64+i.val); omega) (by change 4+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_72 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 4+8*(72+i.val); omega) (by change 4+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_80 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 4+8*(80+i.val); omega) (by change 4+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_88 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 4+8*(88+i.val); omega) (by change 4+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_96 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 4+8*(96+i.val); omega) (by change 4+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_104 (i : Fin 8) :
    source0_4Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_4Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 4+8*(104+i.val); omega) (by change 4+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_4_all (i : Fin 112) : source0_4Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_4_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_4_104 _

private def source0_5Pred (i : Fin 112) : Prop :=
  (generatorRows 5).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(5 : Fin 8)))

attribute [local irreducible] source0_5Pred

private theorem source0_5_0 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 5+8*(0+i.val); omega) (by change 5+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_8 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 5+8*(8+i.val); omega) (by change 5+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_16 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 5+8*(16+i.val); omega) (by change 5+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_24 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 5+8*(24+i.val); omega) (by change 5+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_32 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 5+8*(32+i.val); omega) (by change 5+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_40 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 5+8*(40+i.val); omega) (by change 5+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_48 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 5+8*(48+i.val); omega) (by change 5+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_56 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 5+8*(56+i.val); omega) (by change 5+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_64 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 5+8*(64+i.val); omega) (by change 5+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_72 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 5+8*(72+i.val); omega) (by change 5+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_80 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 5+8*(80+i.val); omega) (by change 5+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_88 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 5+8*(88+i.val); omega) (by change 5+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_96 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 5+8*(96+i.val); omega) (by change 5+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_104 (i : Fin 8) :
    source0_5Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_5Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 5+8*(104+i.val); omega) (by change 5+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_5_all (i : Fin 112) : source0_5Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_5_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_5_104 _

private def source0_6Pred (i : Fin 112) : Prop :=
  (generatorRows 6).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(6 : Fin 8)))

attribute [local irreducible] source0_6Pred

private theorem source0_6_0 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 6+8*(0+i.val); omega) (by change 6+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_8 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 6+8*(8+i.val); omega) (by change 6+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_16 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 6+8*(16+i.val); omega) (by change 6+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_24 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 6+8*(24+i.val); omega) (by change 6+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_32 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 6+8*(32+i.val); omega) (by change 6+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_40 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 6+8*(40+i.val); omega) (by change 6+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_48 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 6+8*(48+i.val); omega) (by change 6+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_56 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 6+8*(56+i.val); omega) (by change 6+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_64 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 6+8*(64+i.val); omega) (by change 6+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_72 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 6+8*(72+i.val); omega) (by change 6+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_80 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 6+8*(80+i.val); omega) (by change 6+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_88 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 6+8*(88+i.val); omega) (by change 6+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_96 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 6+8*(96+i.val); omega) (by change 6+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_104 (i : Fin 8) :
    source0_6Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_6Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 6+8*(104+i.val); omega) (by change 6+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_6_all (i : Fin 112) : source0_6Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_6_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_6_104 _

private def source0_7Pred (i : Fin 112) : Prop :=
  (generatorRows 7).get i ^^^ 2^i.val = step0Rows.get (finProdFinEquiv (i,(7 : Fin 8)))

attribute [local irreducible] source0_7Pred

private theorem source0_7_0 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 0 (Fin.castAdd 104 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 7+8*(0+i.val); omega) (by change 7+8*(0+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_8 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 8 (Fin.castAdd 96 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 7+8*(8+i.val); omega) (by change 7+8*(8+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_16 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 16 (Fin.castAdd 88 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 7+8*(16+i.val); omega) (by change 7+8*(16+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_24 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 24 (Fin.castAdd 80 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 7+8*(24+i.val); omega) (by change 7+8*(24+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_32 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 32 (Fin.castAdd 72 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 7+8*(32+i.val); omega) (by change 7+8*(32+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_40 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 40 (Fin.castAdd 64 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 7+8*(40+i.val); omega) (by change 7+8*(40+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_48 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 48 (Fin.castAdd 56 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 7+8*(48+i.val); omega) (by change 7+8*(48+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_56 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 56 (Fin.castAdd 48 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 7+8*(56+i.val); omega) (by change 7+8*(56+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_64 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 64 (Fin.castAdd 40 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 7+8*(64+i.val); omega) (by change 7+8*(64+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_72 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 72 (Fin.castAdd 32 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 7+8*(72+i.val); omega) (by change 7+8*(72+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_80 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 80 (Fin.castAdd 24 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 7+8*(80+i.val); omega) (by change 7+8*(80+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_88 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 88 (Fin.castAdd 16 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 7+8*(88+i.val); omega) (by change 7+8*(88+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_96 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 96 (Fin.castAdd 8 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 7+8*(96+i.val); omega) (by change 7+8*(96+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_104 (i : Fin 8) :
    source0_7Pred (Fin.natAdd 104 (Fin.castAdd 0 i)) := by
  unfold source0_7Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 7+8*(104+i.val); omega) (by change 7+8*(104+i.val) < _; omega)]
  fin_cases i <;> decide +kernel

private theorem source0_7_all (i : Fin 112) : source0_7Pred i := by
  by_cases h0 : i.val < 8
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 104 (⟨i.val-0, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_0 _
  by_cases h8 : i.val < 16
  · have he : i = (Fin.natAdd 8 (Fin.castAdd 96 (⟨i.val-8, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_8 _
  by_cases h16 : i.val < 24
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 88 (⟨i.val-16, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_16 _
  by_cases h24 : i.val < 32
  · have he : i = (Fin.natAdd 24 (Fin.castAdd 80 (⟨i.val-24, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_24 _
  by_cases h32 : i.val < 40
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 72 (⟨i.val-32, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_32 _
  by_cases h40 : i.val < 48
  · have he : i = (Fin.natAdd 40 (Fin.castAdd 64 (⟨i.val-40, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_40 _
  by_cases h48 : i.val < 56
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 56 (⟨i.val-48, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_48 _
  by_cases h56 : i.val < 64
  · have he : i = (Fin.natAdd 56 (Fin.castAdd 48 (⟨i.val-56, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_56 _
  by_cases h64 : i.val < 72
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 40 (⟨i.val-64, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_64 _
  by_cases h72 : i.val < 80
  · have he : i = (Fin.natAdd 72 (Fin.castAdd 32 (⟨i.val-72, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_72 _
  by_cases h80 : i.val < 88
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 24 (⟨i.val-80, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_80 _
  by_cases h88 : i.val < 96
  · have he : i = (Fin.natAdd 88 (Fin.castAdd 16 (⟨i.val-88, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_88 _
  by_cases h96 : i.val < 104
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 8 (⟨i.val-96, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact source0_7_96 _
  have he : i = (Fin.natAdd 104 (Fin.castAdd 0 (⟨i.val-104, by omega⟩ : Fin 8))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact source0_7_104 _

theorem step0_source (i : Fin 112) (j : Fin 8) :
    packedRow (packedOne.get i) (generatorRows j) ^^^ packedOne.get i =
      step0Rows.get (finProdFinEquiv (i,j)) := by
  rw [packedOne_get, packedRow_pow]
  have hj : ∀ j : Fin 8, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by decide +kernel
  rcases hj j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [source0_0Pred] using source0_0_all i
  · simpa only [source0_1Pred] using source0_1_all i
  · simpa only [source0_2Pred] using source0_2_all i
  · simpa only [source0_3Pred] using source0_3_all i
  · simpa only [source0_4Pred] using source0_4_all i
  · simpa only [source0_5Pred] using source0_5_all i
  · simpa only [source0_6Pred] using source0_6_all i
  · simpa only [source0_7Pred] using source0_7_all i

private def forward0Pred (i : Fin 896) : Prop :=
  step0Rows.get i = combine layer1Rows (forward0.get i)

attribute [local irreducible] forward0Pred

private theorem forward0_0 (i : Fin 16) :
    forward0Pred (Fin.natAdd 0 (Fin.castAdd 880 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  rw [forward0_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_16 (i : Fin 16) :
    forward0Pred (Fin.natAdd 16 (Fin.castAdd 864 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  rw [forward0_chunk0 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_32 (i : Fin 16) :
    forward0Pred (Fin.natAdd 32 (Fin.castAdd 848 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  rw [forward0_chunk0 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_48 (i : Fin 16) :
    forward0Pred (Fin.natAdd 48 (Fin.castAdd 832 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  rw [forward0_chunk0 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_64 (i : Fin 16) :
    forward0Pred (Fin.natAdd 64 (Fin.castAdd 816 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  rw [forward0_chunk1 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_80 (i : Fin 16) :
    forward0Pred (Fin.natAdd 80 (Fin.castAdd 800 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  rw [forward0_chunk1 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_96 (i : Fin 16) :
    forward0Pred (Fin.natAdd 96 (Fin.castAdd 784 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  rw [forward0_chunk1 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_112 (i : Fin 16) :
    forward0Pred (Fin.natAdd 112 (Fin.castAdd 768 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  rw [forward0_chunk1 _ (by change _ ≤ 112+i.val; omega) (by change 112+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_128 (i : Fin 16) :
    forward0Pred (Fin.natAdd 128 (Fin.castAdd 752 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  rw [forward0_chunk2 _ (by change _ ≤ 128+i.val; omega) (by change 128+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_144 (i : Fin 16) :
    forward0Pred (Fin.natAdd 144 (Fin.castAdd 736 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  rw [forward0_chunk2 _ (by change _ ≤ 144+i.val; omega) (by change 144+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_160 (i : Fin 16) :
    forward0Pred (Fin.natAdd 160 (Fin.castAdd 720 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  rw [forward0_chunk2 _ (by change _ ≤ 160+i.val; omega) (by change 160+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_176 (i : Fin 16) :
    forward0Pred (Fin.natAdd 176 (Fin.castAdd 704 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  rw [forward0_chunk2 _ (by change _ ≤ 176+i.val; omega) (by change 176+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_192 (i : Fin 16) :
    forward0Pred (Fin.natAdd 192 (Fin.castAdd 688 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  rw [forward0_chunk3 _ (by change _ ≤ 192+i.val; omega) (by change 192+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_208 (i : Fin 16) :
    forward0Pred (Fin.natAdd 208 (Fin.castAdd 672 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  rw [forward0_chunk3 _ (by change _ ≤ 208+i.val; omega) (by change 208+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_224 (i : Fin 16) :
    forward0Pred (Fin.natAdd 224 (Fin.castAdd 656 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  rw [forward0_chunk3 _ (by change _ ≤ 224+i.val; omega) (by change 224+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_240 (i : Fin 16) :
    forward0Pred (Fin.natAdd 240 (Fin.castAdd 640 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  rw [forward0_chunk3 _ (by change _ ≤ 240+i.val; omega) (by change 240+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_256 (i : Fin 16) :
    forward0Pred (Fin.natAdd 256 (Fin.castAdd 624 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 256+i.val; omega) (by change 256+i.val < _; omega)]
  rw [forward0_chunk4 _ (by change _ ≤ 256+i.val; omega) (by change 256+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_272 (i : Fin 16) :
    forward0Pred (Fin.natAdd 272 (Fin.castAdd 608 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 272+i.val; omega) (by change 272+i.val < _; omega)]
  rw [forward0_chunk4 _ (by change _ ≤ 272+i.val; omega) (by change 272+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_288 (i : Fin 16) :
    forward0Pred (Fin.natAdd 288 (Fin.castAdd 592 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 288+i.val; omega) (by change 288+i.val < _; omega)]
  rw [forward0_chunk4 _ (by change _ ≤ 288+i.val; omega) (by change 288+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_304 (i : Fin 16) :
    forward0Pred (Fin.natAdd 304 (Fin.castAdd 576 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk4 _ (by change _ ≤ 304+i.val; omega) (by change 304+i.val < _; omega)]
  rw [forward0_chunk4 _ (by change _ ≤ 304+i.val; omega) (by change 304+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_320 (i : Fin 16) :
    forward0Pred (Fin.natAdd 320 (Fin.castAdd 560 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 320+i.val; omega) (by change 320+i.val < _; omega)]
  rw [forward0_chunk5 _ (by change _ ≤ 320+i.val; omega) (by change 320+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_336 (i : Fin 16) :
    forward0Pred (Fin.natAdd 336 (Fin.castAdd 544 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 336+i.val; omega) (by change 336+i.val < _; omega)]
  rw [forward0_chunk5 _ (by change _ ≤ 336+i.val; omega) (by change 336+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_352 (i : Fin 16) :
    forward0Pred (Fin.natAdd 352 (Fin.castAdd 528 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 352+i.val; omega) (by change 352+i.val < _; omega)]
  rw [forward0_chunk5 _ (by change _ ≤ 352+i.val; omega) (by change 352+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_368 (i : Fin 16) :
    forward0Pred (Fin.natAdd 368 (Fin.castAdd 512 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk5 _ (by change _ ≤ 368+i.val; omega) (by change 368+i.val < _; omega)]
  rw [forward0_chunk5 _ (by change _ ≤ 368+i.val; omega) (by change 368+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_384 (i : Fin 16) :
    forward0Pred (Fin.natAdd 384 (Fin.castAdd 496 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 384+i.val; omega) (by change 384+i.val < _; omega)]
  rw [forward0_chunk6 _ (by change _ ≤ 384+i.val; omega) (by change 384+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_400 (i : Fin 16) :
    forward0Pred (Fin.natAdd 400 (Fin.castAdd 480 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 400+i.val; omega) (by change 400+i.val < _; omega)]
  rw [forward0_chunk6 _ (by change _ ≤ 400+i.val; omega) (by change 400+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_416 (i : Fin 16) :
    forward0Pred (Fin.natAdd 416 (Fin.castAdd 464 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 416+i.val; omega) (by change 416+i.val < _; omega)]
  rw [forward0_chunk6 _ (by change _ ≤ 416+i.val; omega) (by change 416+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_432 (i : Fin 16) :
    forward0Pred (Fin.natAdd 432 (Fin.castAdd 448 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk6 _ (by change _ ≤ 432+i.val; omega) (by change 432+i.val < _; omega)]
  rw [forward0_chunk6 _ (by change _ ≤ 432+i.val; omega) (by change 432+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_448 (i : Fin 16) :
    forward0Pred (Fin.natAdd 448 (Fin.castAdd 432 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 448+i.val; omega) (by change 448+i.val < _; omega)]
  rw [forward0_chunk7 _ (by change _ ≤ 448+i.val; omega) (by change 448+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_464 (i : Fin 16) :
    forward0Pred (Fin.natAdd 464 (Fin.castAdd 416 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 464+i.val; omega) (by change 464+i.val < _; omega)]
  rw [forward0_chunk7 _ (by change _ ≤ 464+i.val; omega) (by change 464+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_480 (i : Fin 16) :
    forward0Pred (Fin.natAdd 480 (Fin.castAdd 400 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 480+i.val; omega) (by change 480+i.val < _; omega)]
  rw [forward0_chunk7 _ (by change _ ≤ 480+i.val; omega) (by change 480+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_496 (i : Fin 16) :
    forward0Pred (Fin.natAdd 496 (Fin.castAdd 384 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk7 _ (by change _ ≤ 496+i.val; omega) (by change 496+i.val < _; omega)]
  rw [forward0_chunk7 _ (by change _ ≤ 496+i.val; omega) (by change 496+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_512 (i : Fin 16) :
    forward0Pred (Fin.natAdd 512 (Fin.castAdd 368 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 512+i.val; omega) (by change 512+i.val < _; omega)]
  rw [forward0_chunk8 _ (by change _ ≤ 512+i.val; omega) (by change 512+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_528 (i : Fin 16) :
    forward0Pred (Fin.natAdd 528 (Fin.castAdd 352 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 528+i.val; omega) (by change 528+i.val < _; omega)]
  rw [forward0_chunk8 _ (by change _ ≤ 528+i.val; omega) (by change 528+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_544 (i : Fin 16) :
    forward0Pred (Fin.natAdd 544 (Fin.castAdd 336 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 544+i.val; omega) (by change 544+i.val < _; omega)]
  rw [forward0_chunk8 _ (by change _ ≤ 544+i.val; omega) (by change 544+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_560 (i : Fin 16) :
    forward0Pred (Fin.natAdd 560 (Fin.castAdd 320 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk8 _ (by change _ ≤ 560+i.val; omega) (by change 560+i.val < _; omega)]
  rw [forward0_chunk8 _ (by change _ ≤ 560+i.val; omega) (by change 560+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_576 (i : Fin 16) :
    forward0Pred (Fin.natAdd 576 (Fin.castAdd 304 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 576+i.val; omega) (by change 576+i.val < _; omega)]
  rw [forward0_chunk9 _ (by change _ ≤ 576+i.val; omega) (by change 576+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_592 (i : Fin 16) :
    forward0Pred (Fin.natAdd 592 (Fin.castAdd 288 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 592+i.val; omega) (by change 592+i.val < _; omega)]
  rw [forward0_chunk9 _ (by change _ ≤ 592+i.val; omega) (by change 592+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_608 (i : Fin 16) :
    forward0Pred (Fin.natAdd 608 (Fin.castAdd 272 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 608+i.val; omega) (by change 608+i.val < _; omega)]
  rw [forward0_chunk9 _ (by change _ ≤ 608+i.val; omega) (by change 608+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_624 (i : Fin 16) :
    forward0Pred (Fin.natAdd 624 (Fin.castAdd 256 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk9 _ (by change _ ≤ 624+i.val; omega) (by change 624+i.val < _; omega)]
  rw [forward0_chunk9 _ (by change _ ≤ 624+i.val; omega) (by change 624+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_640 (i : Fin 16) :
    forward0Pred (Fin.natAdd 640 (Fin.castAdd 240 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 640+i.val; omega) (by change 640+i.val < _; omega)]
  rw [forward0_chunk10 _ (by change _ ≤ 640+i.val; omega) (by change 640+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_656 (i : Fin 16) :
    forward0Pred (Fin.natAdd 656 (Fin.castAdd 224 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 656+i.val; omega) (by change 656+i.val < _; omega)]
  rw [forward0_chunk10 _ (by change _ ≤ 656+i.val; omega) (by change 656+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_672 (i : Fin 16) :
    forward0Pred (Fin.natAdd 672 (Fin.castAdd 208 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 672+i.val; omega) (by change 672+i.val < _; omega)]
  rw [forward0_chunk10 _ (by change _ ≤ 672+i.val; omega) (by change 672+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_688 (i : Fin 16) :
    forward0Pred (Fin.natAdd 688 (Fin.castAdd 192 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk10 _ (by change _ ≤ 688+i.val; omega) (by change 688+i.val < _; omega)]
  rw [forward0_chunk10 _ (by change _ ≤ 688+i.val; omega) (by change 688+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_704 (i : Fin 16) :
    forward0Pred (Fin.natAdd 704 (Fin.castAdd 176 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 704+i.val; omega) (by change 704+i.val < _; omega)]
  rw [forward0_chunk11 _ (by change _ ≤ 704+i.val; omega) (by change 704+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_720 (i : Fin 16) :
    forward0Pred (Fin.natAdd 720 (Fin.castAdd 160 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 720+i.val; omega) (by change 720+i.val < _; omega)]
  rw [forward0_chunk11 _ (by change _ ≤ 720+i.val; omega) (by change 720+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_736 (i : Fin 16) :
    forward0Pred (Fin.natAdd 736 (Fin.castAdd 144 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 736+i.val; omega) (by change 736+i.val < _; omega)]
  rw [forward0_chunk11 _ (by change _ ≤ 736+i.val; omega) (by change 736+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_752 (i : Fin 16) :
    forward0Pred (Fin.natAdd 752 (Fin.castAdd 128 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk11 _ (by change _ ≤ 752+i.val; omega) (by change 752+i.val < _; omega)]
  rw [forward0_chunk11 _ (by change _ ≤ 752+i.val; omega) (by change 752+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_768 (i : Fin 16) :
    forward0Pred (Fin.natAdd 768 (Fin.castAdd 112 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 768+i.val; omega) (by change 768+i.val < _; omega)]
  rw [forward0_chunk12 _ (by change _ ≤ 768+i.val; omega) (by change 768+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_784 (i : Fin 16) :
    forward0Pred (Fin.natAdd 784 (Fin.castAdd 96 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 784+i.val; omega) (by change 784+i.val < _; omega)]
  rw [forward0_chunk12 _ (by change _ ≤ 784+i.val; omega) (by change 784+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_800 (i : Fin 16) :
    forward0Pred (Fin.natAdd 800 (Fin.castAdd 80 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 800+i.val; omega) (by change 800+i.val < _; omega)]
  rw [forward0_chunk12 _ (by change _ ≤ 800+i.val; omega) (by change 800+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_816 (i : Fin 16) :
    forward0Pred (Fin.natAdd 816 (Fin.castAdd 64 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk12 _ (by change _ ≤ 816+i.val; omega) (by change 816+i.val < _; omega)]
  rw [forward0_chunk12 _ (by change _ ≤ 816+i.val; omega) (by change 816+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_832 (i : Fin 16) :
    forward0Pred (Fin.natAdd 832 (Fin.castAdd 48 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 832+i.val; omega) (by change 832+i.val < _; omega)]
  rw [forward0_chunk13 _ (by change _ ≤ 832+i.val; omega) (by change 832+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_848 (i : Fin 16) :
    forward0Pred (Fin.natAdd 848 (Fin.castAdd 32 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 848+i.val; omega) (by change 848+i.val < _; omega)]
  rw [forward0_chunk13 _ (by change _ ≤ 848+i.val; omega) (by change 848+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_864 (i : Fin 16) :
    forward0Pred (Fin.natAdd 864 (Fin.castAdd 16 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 864+i.val; omega) (by change 864+i.val < _; omega)]
  rw [forward0_chunk13 _ (by change _ ≤ 864+i.val; omega) (by change 864+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_880 (i : Fin 16) :
    forward0Pred (Fin.natAdd 880 (Fin.castAdd 0 i)) := by
  unfold forward0Pred
  rw [step0Rows_chunk13 _ (by change _ ≤ 880+i.val; omega) (by change 880+i.val < _; omega)]
  rw [forward0_chunk13 _ (by change _ ≤ 880+i.val; omega) (by change 880+i.val < _; omega)]
  fin_cases i <;> decide +kernel

private theorem forward0_all (i : Fin 896) : forward0Pred i := by
  by_cases h0 : i.val < 16
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 880 (⟨i.val-0, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_0 _
  by_cases h16 : i.val < 32
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 864 (⟨i.val-16, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_16 _
  by_cases h32 : i.val < 48
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 848 (⟨i.val-32, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_32 _
  by_cases h48 : i.val < 64
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 832 (⟨i.val-48, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_48 _
  by_cases h64 : i.val < 80
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 816 (⟨i.val-64, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_64 _
  by_cases h80 : i.val < 96
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 800 (⟨i.val-80, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_80 _
  by_cases h96 : i.val < 112
  · have he : i = (Fin.natAdd 96 (Fin.castAdd 784 (⟨i.val-96, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_96 _
  by_cases h112 : i.val < 128
  · have he : i = (Fin.natAdd 112 (Fin.castAdd 768 (⟨i.val-112, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_112 _
  by_cases h128 : i.val < 144
  · have he : i = (Fin.natAdd 128 (Fin.castAdd 752 (⟨i.val-128, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_128 _
  by_cases h144 : i.val < 160
  · have he : i = (Fin.natAdd 144 (Fin.castAdd 736 (⟨i.val-144, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_144 _
  by_cases h160 : i.val < 176
  · have he : i = (Fin.natAdd 160 (Fin.castAdd 720 (⟨i.val-160, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_160 _
  by_cases h176 : i.val < 192
  · have he : i = (Fin.natAdd 176 (Fin.castAdd 704 (⟨i.val-176, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_176 _
  by_cases h192 : i.val < 208
  · have he : i = (Fin.natAdd 192 (Fin.castAdd 688 (⟨i.val-192, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_192 _
  by_cases h208 : i.val < 224
  · have he : i = (Fin.natAdd 208 (Fin.castAdd 672 (⟨i.val-208, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_208 _
  by_cases h224 : i.val < 240
  · have he : i = (Fin.natAdd 224 (Fin.castAdd 656 (⟨i.val-224, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_224 _
  by_cases h240 : i.val < 256
  · have he : i = (Fin.natAdd 240 (Fin.castAdd 640 (⟨i.val-240, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_240 _
  by_cases h256 : i.val < 272
  · have he : i = (Fin.natAdd 256 (Fin.castAdd 624 (⟨i.val-256, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_256 _
  by_cases h272 : i.val < 288
  · have he : i = (Fin.natAdd 272 (Fin.castAdd 608 (⟨i.val-272, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_272 _
  by_cases h288 : i.val < 304
  · have he : i = (Fin.natAdd 288 (Fin.castAdd 592 (⟨i.val-288, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_288 _
  by_cases h304 : i.val < 320
  · have he : i = (Fin.natAdd 304 (Fin.castAdd 576 (⟨i.val-304, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_304 _
  by_cases h320 : i.val < 336
  · have he : i = (Fin.natAdd 320 (Fin.castAdd 560 (⟨i.val-320, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_320 _
  by_cases h336 : i.val < 352
  · have he : i = (Fin.natAdd 336 (Fin.castAdd 544 (⟨i.val-336, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_336 _
  by_cases h352 : i.val < 368
  · have he : i = (Fin.natAdd 352 (Fin.castAdd 528 (⟨i.val-352, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_352 _
  by_cases h368 : i.val < 384
  · have he : i = (Fin.natAdd 368 (Fin.castAdd 512 (⟨i.val-368, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_368 _
  by_cases h384 : i.val < 400
  · have he : i = (Fin.natAdd 384 (Fin.castAdd 496 (⟨i.val-384, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_384 _
  by_cases h400 : i.val < 416
  · have he : i = (Fin.natAdd 400 (Fin.castAdd 480 (⟨i.val-400, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_400 _
  by_cases h416 : i.val < 432
  · have he : i = (Fin.natAdd 416 (Fin.castAdd 464 (⟨i.val-416, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_416 _
  by_cases h432 : i.val < 448
  · have he : i = (Fin.natAdd 432 (Fin.castAdd 448 (⟨i.val-432, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_432 _
  by_cases h448 : i.val < 464
  · have he : i = (Fin.natAdd 448 (Fin.castAdd 432 (⟨i.val-448, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_448 _
  by_cases h464 : i.val < 480
  · have he : i = (Fin.natAdd 464 (Fin.castAdd 416 (⟨i.val-464, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_464 _
  by_cases h480 : i.val < 496
  · have he : i = (Fin.natAdd 480 (Fin.castAdd 400 (⟨i.val-480, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_480 _
  by_cases h496 : i.val < 512
  · have he : i = (Fin.natAdd 496 (Fin.castAdd 384 (⟨i.val-496, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_496 _
  by_cases h512 : i.val < 528
  · have he : i = (Fin.natAdd 512 (Fin.castAdd 368 (⟨i.val-512, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_512 _
  by_cases h528 : i.val < 544
  · have he : i = (Fin.natAdd 528 (Fin.castAdd 352 (⟨i.val-528, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_528 _
  by_cases h544 : i.val < 560
  · have he : i = (Fin.natAdd 544 (Fin.castAdd 336 (⟨i.val-544, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_544 _
  by_cases h560 : i.val < 576
  · have he : i = (Fin.natAdd 560 (Fin.castAdd 320 (⟨i.val-560, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_560 _
  by_cases h576 : i.val < 592
  · have he : i = (Fin.natAdd 576 (Fin.castAdd 304 (⟨i.val-576, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_576 _
  by_cases h592 : i.val < 608
  · have he : i = (Fin.natAdd 592 (Fin.castAdd 288 (⟨i.val-592, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_592 _
  by_cases h608 : i.val < 624
  · have he : i = (Fin.natAdd 608 (Fin.castAdd 272 (⟨i.val-608, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_608 _
  by_cases h624 : i.val < 640
  · have he : i = (Fin.natAdd 624 (Fin.castAdd 256 (⟨i.val-624, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_624 _
  by_cases h640 : i.val < 656
  · have he : i = (Fin.natAdd 640 (Fin.castAdd 240 (⟨i.val-640, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_640 _
  by_cases h656 : i.val < 672
  · have he : i = (Fin.natAdd 656 (Fin.castAdd 224 (⟨i.val-656, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_656 _
  by_cases h672 : i.val < 688
  · have he : i = (Fin.natAdd 672 (Fin.castAdd 208 (⟨i.val-672, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_672 _
  by_cases h688 : i.val < 704
  · have he : i = (Fin.natAdd 688 (Fin.castAdd 192 (⟨i.val-688, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_688 _
  by_cases h704 : i.val < 720
  · have he : i = (Fin.natAdd 704 (Fin.castAdd 176 (⟨i.val-704, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_704 _
  by_cases h720 : i.val < 736
  · have he : i = (Fin.natAdd 720 (Fin.castAdd 160 (⟨i.val-720, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_720 _
  by_cases h736 : i.val < 752
  · have he : i = (Fin.natAdd 736 (Fin.castAdd 144 (⟨i.val-736, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_736 _
  by_cases h752 : i.val < 768
  · have he : i = (Fin.natAdd 752 (Fin.castAdd 128 (⟨i.val-752, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_752 _
  by_cases h768 : i.val < 784
  · have he : i = (Fin.natAdd 768 (Fin.castAdd 112 (⟨i.val-768, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_768 _
  by_cases h784 : i.val < 800
  · have he : i = (Fin.natAdd 784 (Fin.castAdd 96 (⟨i.val-784, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_784 _
  by_cases h800 : i.val < 816
  · have he : i = (Fin.natAdd 800 (Fin.castAdd 80 (⟨i.val-800, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_800 _
  by_cases h816 : i.val < 832
  · have he : i = (Fin.natAdd 816 (Fin.castAdd 64 (⟨i.val-816, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_816 _
  by_cases h832 : i.val < 848
  · have he : i = (Fin.natAdd 832 (Fin.castAdd 48 (⟨i.val-832, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_832 _
  by_cases h848 : i.val < 864
  · have he : i = (Fin.natAdd 848 (Fin.castAdd 32 (⟨i.val-848, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_848 _
  by_cases h864 : i.val < 880
  · have he : i = (Fin.natAdd 864 (Fin.castAdd 16 (⟨i.val-864, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact forward0_864 _
  have he : i = (Fin.natAdd 880 (Fin.castAdd 0 (⟨i.val-880, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact forward0_880 _

theorem step0_forward (i : Fin 896) : step0Rows.get i =
    combine layer1Rows (forward0.get i) := by
  simpa only [forward0Pred] using forward0_all i

private def reverse0Pred (i : Fin 101) : Prop :=
  layer1Rows.get i = sparseCombine step0Rows (reverse0Sparse.get i)

attribute [local irreducible] reverse0Pred

private theorem reverse0_0 (i : Fin 16) :
    reverse0Pred (Fin.natAdd 0 (Fin.castAdd 85 i)) := by
  unfold reverse0Pred
  rw [reverse0Sparse_chunk0 _ (by change _ ≤ 0+i.val; omega) (by change 0+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step0Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse0_16 (i : Fin 16) :
    reverse0Pred (Fin.natAdd 16 (Fin.castAdd 69 i)) := by
  unfold reverse0Pred
  rw [reverse0Sparse_chunk1 _ (by change _ ≤ 16+i.val; omega) (by change 16+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step0Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse0_32 (i : Fin 16) :
    reverse0Pred (Fin.natAdd 32 (Fin.castAdd 53 i)) := by
  unfold reverse0Pred
  rw [reverse0Sparse_chunk2 _ (by change _ ≤ 32+i.val; omega) (by change 32+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step0Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse0_48 (i : Fin 16) :
    reverse0Pred (Fin.natAdd 48 (Fin.castAdd 37 i)) := by
  unfold reverse0Pred
  rw [reverse0Sparse_chunk3 _ (by change _ ≤ 48+i.val; omega) (by change 48+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step0Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse0_64 (i : Fin 16) :
    reverse0Pred (Fin.natAdd 64 (Fin.castAdd 21 i)) := by
  unfold reverse0Pred
  rw [reverse0Sparse_chunk4 _ (by change _ ≤ 64+i.val; omega) (by change 64+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step0Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse0_80 (i : Fin 16) :
    reverse0Pred (Fin.natAdd 80 (Fin.castAdd 5 i)) := by
  unfold reverse0Pred
  rw [reverse0Sparse_chunk5 _ (by change _ ≤ 80+i.val; omega) (by change 80+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step0Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse0_96 (i : Fin 5) :
    reverse0Pred (Fin.natAdd 96 (Fin.castAdd 0 i)) := by
  unfold reverse0Pred
  rw [reverse0Sparse_chunk6 _ (by change _ ≤ 96+i.val; omega) (by change 96+i.val < _; omega)]
  unfold sparseCombine
  conv_rhs => arg 1; arg 1; ext j; rw [step0Rows_get]
  fin_cases i <;> decide +kernel

private theorem reverse0_all (i : Fin 101) : reverse0Pred i := by
  by_cases h0 : i.val < 16
  · have he : i = (Fin.natAdd 0 (Fin.castAdd 85 (⟨i.val-0, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse0_0 _
  by_cases h16 : i.val < 32
  · have he : i = (Fin.natAdd 16 (Fin.castAdd 69 (⟨i.val-16, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse0_16 _
  by_cases h32 : i.val < 48
  · have he : i = (Fin.natAdd 32 (Fin.castAdd 53 (⟨i.val-32, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse0_32 _
  by_cases h48 : i.val < 64
  · have he : i = (Fin.natAdd 48 (Fin.castAdd 37 (⟨i.val-48, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse0_48 _
  by_cases h64 : i.val < 80
  · have he : i = (Fin.natAdd 64 (Fin.castAdd 21 (⟨i.val-64, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse0_64 _
  by_cases h80 : i.val < 96
  · have he : i = (Fin.natAdd 80 (Fin.castAdd 5 (⟨i.val-80, by omega⟩ : Fin 16))) := Fin.ext (by dsimp; omega)
    rw [he]
    exact reverse0_80 _
  have he : i = (Fin.natAdd 96 (Fin.castAdd 0 (⟨i.val-96, by omega⟩ : Fin 5))) := Fin.ext (by dsimp; omega)
  rw [he]
  exact reverse0_96 _

theorem step0_reverse (i : Fin 101) : layer1Rows.get i =
    sparseCombine step0Rows (reverse0Sparse.get i) := by
  simpa only [reverse0Pred] using reverse0_all i

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
