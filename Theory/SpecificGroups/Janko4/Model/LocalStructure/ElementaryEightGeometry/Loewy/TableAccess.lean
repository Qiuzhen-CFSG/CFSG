module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.SparseRows

/-! Structural table access avoids reducing concatenation during each arithmetic
certificate. The lemmas only reassociate lookup; all entries are unchanged. -/
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxErrors 1
public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
private theorem get_append_left {α : Type} {n m : ℕ} (a : Vector α n) (b : Vector α m)
    (i : Fin (n+m)) (h : i.val < n) :
    (a.append b).get i = a.get ⟨i.val,h⟩ :=
  Vector.getElem_append_left h
private theorem get_append_right {α : Type} {n m : ℕ} (a : Vector α n) (b : Vector α m)
    (i : Fin (n+m)) (h : n ≤ i.val) :
    (a.append b).get i = b.get ⟨i.val-n, by omega⟩ :=
  Vector.getElem_append_right i.isLt h
attribute [local irreducible] layer1RowsChunk0 layer1RowsChunk1
theorem layer1Rows_chunk0 (i : Fin 101) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    layer1Rows.get i = layer1RowsChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold layer1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem layer1Rows_chunk1 (i : Fin 101) (_hl : 64 ≤ i.val) (_hh : i.val < 101) :
    layer1Rows.get i = layer1RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  unfold layer1Rows
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem layer1Rows_get (i : Fin 101) : layer1Rows.get i =
    if h0 : i.val < 64 then layer1RowsChunk0.get ⟨i.val-0, by omega⟩ else
      layer1RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact layer1Rows_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  exact layer1Rows_chunk1 i (by omega) (by omega)

attribute [local irreducible] layer2RowsChunk0 layer2RowsChunk1
theorem layer2Rows_chunk0 (i : Fin 76) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    layer2Rows.get i = layer2RowsChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold layer2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem layer2Rows_chunk1 (i : Fin 76) (_hl : 64 ≤ i.val) (_hh : i.val < 76) :
    layer2Rows.get i = layer2RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  unfold layer2Rows
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem layer2Rows_get (i : Fin 76) : layer2Rows.get i =
    if h0 : i.val < 64 then layer2RowsChunk0.get ⟨i.val-0, by omega⟩ else
      layer2RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact layer2Rows_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  exact layer2Rows_chunk1 i (by omega) (by omega)

attribute [local irreducible] step0RowsChunk0 step0RowsChunk1 step0RowsChunk2 step0RowsChunk3 step0RowsChunk4 step0RowsChunk5 step0RowsChunk6 step0RowsChunk7 step0RowsChunk8 step0RowsChunk9 step0RowsChunk10 step0RowsChunk11 step0RowsChunk12 step0RowsChunk13
theorem step0Rows_chunk0 (i : Fin 896) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    step0Rows.get i = step0RowsChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem step0Rows_chunk1 (i : Fin 896) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    step0Rows.get i = step0RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk2 (i : Fin 896) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    step0Rows.get i = step0RowsChunk2.get ⟨i.val-128, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk3 (i : Fin 896) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    step0Rows.get i = step0RowsChunk3.get ⟨i.val-192, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk4 (i : Fin 896) (_hl : 256 ≤ i.val) (_hh : i.val < 320) :
    step0Rows.get i = step0RowsChunk4.get ⟨i.val-256, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk5 (i : Fin 896) (_hl : 320 ≤ i.val) (_hh : i.val < 384) :
    step0Rows.get i = step0RowsChunk5.get ⟨i.val-320, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk6 (i : Fin 896) (_hl : 384 ≤ i.val) (_hh : i.val < 448) :
    step0Rows.get i = step0RowsChunk6.get ⟨i.val-384, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk7 (i : Fin 896) (_hl : 448 ≤ i.val) (_hh : i.val < 512) :
    step0Rows.get i = step0RowsChunk7.get ⟨i.val-448, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk8 (i : Fin 896) (_hl : 512 ≤ i.val) (_hh : i.val < 576) :
    step0Rows.get i = step0RowsChunk8.get ⟨i.val-512, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk9 (i : Fin 896) (_hl : 576 ≤ i.val) (_hh : i.val < 640) :
    step0Rows.get i = step0RowsChunk9.get ⟨i.val-576, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk10 (i : Fin 896) (_hl : 640 ≤ i.val) (_hh : i.val < 704) :
    step0Rows.get i = step0RowsChunk10.get ⟨i.val-640, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk11 (i : Fin 896) (_hl : 704 ≤ i.val) (_hh : i.val < 768) :
    step0Rows.get i = step0RowsChunk11.get ⟨i.val-704, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk12 (i : Fin 896) (_hl : 768 ≤ i.val) (_hh : i.val < 832) :
    step0Rows.get i = step0RowsChunk12.get ⟨i.val-768, by omega⟩ := by
  unfold step0Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_chunk13 (i : Fin 896) (_hl : 832 ≤ i.val) (_hh : i.val < 896) :
    step0Rows.get i = step0RowsChunk13.get ⟨i.val-832, by omega⟩ := by
  unfold step0Rows
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step0Rows_get (i : Fin 896) : step0Rows.get i =
    if h0 : i.val < 64 then step0RowsChunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then step0RowsChunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then step0RowsChunk2.get ⟨i.val-128, by omega⟩ else
          if h3 : i.val < 256 then step0RowsChunk3.get ⟨i.val-192, by omega⟩ else
            if h4 : i.val < 320 then step0RowsChunk4.get ⟨i.val-256, by omega⟩ else
              if h5 : i.val < 384 then step0RowsChunk5.get ⟨i.val-320, by omega⟩ else
                if h6 : i.val < 448 then step0RowsChunk6.get ⟨i.val-384, by omega⟩ else
                  if h7 : i.val < 512 then step0RowsChunk7.get ⟨i.val-448, by omega⟩ else
                    if h8 : i.val < 576 then step0RowsChunk8.get ⟨i.val-512, by omega⟩ else
                      if h9 : i.val < 640 then step0RowsChunk9.get ⟨i.val-576, by omega⟩ else
                        if h10 : i.val < 704 then step0RowsChunk10.get ⟨i.val-640, by omega⟩ else
                          if h11 : i.val < 768 then step0RowsChunk11.get ⟨i.val-704, by omega⟩ else
                            if h12 : i.val < 832 then step0RowsChunk12.get ⟨i.val-768, by omega⟩ else
                              step0RowsChunk13.get ⟨i.val-832, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact step0Rows_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact step0Rows_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact step0Rows_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 256
  · rw [dif_pos h3]
    exact step0Rows_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  by_cases h4 : i.val < 320
  · rw [dif_pos h4]
    exact step0Rows_chunk4 i (by omega) (by omega)
  rw [dif_neg h4]
  by_cases h5 : i.val < 384
  · rw [dif_pos h5]
    exact step0Rows_chunk5 i (by omega) (by omega)
  rw [dif_neg h5]
  by_cases h6 : i.val < 448
  · rw [dif_pos h6]
    exact step0Rows_chunk6 i (by omega) (by omega)
  rw [dif_neg h6]
  by_cases h7 : i.val < 512
  · rw [dif_pos h7]
    exact step0Rows_chunk7 i (by omega) (by omega)
  rw [dif_neg h7]
  by_cases h8 : i.val < 576
  · rw [dif_pos h8]
    exact step0Rows_chunk8 i (by omega) (by omega)
  rw [dif_neg h8]
  by_cases h9 : i.val < 640
  · rw [dif_pos h9]
    exact step0Rows_chunk9 i (by omega) (by omega)
  rw [dif_neg h9]
  by_cases h10 : i.val < 704
  · rw [dif_pos h10]
    exact step0Rows_chunk10 i (by omega) (by omega)
  rw [dif_neg h10]
  by_cases h11 : i.val < 768
  · rw [dif_pos h11]
    exact step0Rows_chunk11 i (by omega) (by omega)
  rw [dif_neg h11]
  by_cases h12 : i.val < 832
  · rw [dif_pos h12]
    exact step0Rows_chunk12 i (by omega) (by omega)
  rw [dif_neg h12]
  exact step0Rows_chunk13 i (by omega) (by omega)

attribute [local irreducible] forward0Chunk0 forward0Chunk1 forward0Chunk2 forward0Chunk3 forward0Chunk4 forward0Chunk5 forward0Chunk6 forward0Chunk7 forward0Chunk8 forward0Chunk9 forward0Chunk10 forward0Chunk11 forward0Chunk12 forward0Chunk13
theorem forward0_chunk0 (i : Fin 896) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    forward0.get i = forward0Chunk0.get ⟨i.val-0, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem forward0_chunk1 (i : Fin 896) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    forward0.get i = forward0Chunk1.get ⟨i.val-64, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk2 (i : Fin 896) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    forward0.get i = forward0Chunk2.get ⟨i.val-128, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk3 (i : Fin 896) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    forward0.get i = forward0Chunk3.get ⟨i.val-192, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk4 (i : Fin 896) (_hl : 256 ≤ i.val) (_hh : i.val < 320) :
    forward0.get i = forward0Chunk4.get ⟨i.val-256, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk5 (i : Fin 896) (_hl : 320 ≤ i.val) (_hh : i.val < 384) :
    forward0.get i = forward0Chunk5.get ⟨i.val-320, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk6 (i : Fin 896) (_hl : 384 ≤ i.val) (_hh : i.val < 448) :
    forward0.get i = forward0Chunk6.get ⟨i.val-384, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk7 (i : Fin 896) (_hl : 448 ≤ i.val) (_hh : i.val < 512) :
    forward0.get i = forward0Chunk7.get ⟨i.val-448, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk8 (i : Fin 896) (_hl : 512 ≤ i.val) (_hh : i.val < 576) :
    forward0.get i = forward0Chunk8.get ⟨i.val-512, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk9 (i : Fin 896) (_hl : 576 ≤ i.val) (_hh : i.val < 640) :
    forward0.get i = forward0Chunk9.get ⟨i.val-576, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk10 (i : Fin 896) (_hl : 640 ≤ i.val) (_hh : i.val < 704) :
    forward0.get i = forward0Chunk10.get ⟨i.val-640, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk11 (i : Fin 896) (_hl : 704 ≤ i.val) (_hh : i.val < 768) :
    forward0.get i = forward0Chunk11.get ⟨i.val-704, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk12 (i : Fin 896) (_hl : 768 ≤ i.val) (_hh : i.val < 832) :
    forward0.get i = forward0Chunk12.get ⟨i.val-768, by omega⟩ := by
  unfold forward0
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_chunk13 (i : Fin 896) (_hl : 832 ≤ i.val) (_hh : i.val < 896) :
    forward0.get i = forward0Chunk13.get ⟨i.val-832, by omega⟩ := by
  unfold forward0
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward0_get (i : Fin 896) : forward0.get i =
    if h0 : i.val < 64 then forward0Chunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then forward0Chunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then forward0Chunk2.get ⟨i.val-128, by omega⟩ else
          if h3 : i.val < 256 then forward0Chunk3.get ⟨i.val-192, by omega⟩ else
            if h4 : i.val < 320 then forward0Chunk4.get ⟨i.val-256, by omega⟩ else
              if h5 : i.val < 384 then forward0Chunk5.get ⟨i.val-320, by omega⟩ else
                if h6 : i.val < 448 then forward0Chunk6.get ⟨i.val-384, by omega⟩ else
                  if h7 : i.val < 512 then forward0Chunk7.get ⟨i.val-448, by omega⟩ else
                    if h8 : i.val < 576 then forward0Chunk8.get ⟨i.val-512, by omega⟩ else
                      if h9 : i.val < 640 then forward0Chunk9.get ⟨i.val-576, by omega⟩ else
                        if h10 : i.val < 704 then forward0Chunk10.get ⟨i.val-640, by omega⟩ else
                          if h11 : i.val < 768 then forward0Chunk11.get ⟨i.val-704, by omega⟩ else
                            if h12 : i.val < 832 then forward0Chunk12.get ⟨i.val-768, by omega⟩ else
                              forward0Chunk13.get ⟨i.val-832, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact forward0_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact forward0_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact forward0_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 256
  · rw [dif_pos h3]
    exact forward0_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  by_cases h4 : i.val < 320
  · rw [dif_pos h4]
    exact forward0_chunk4 i (by omega) (by omega)
  rw [dif_neg h4]
  by_cases h5 : i.val < 384
  · rw [dif_pos h5]
    exact forward0_chunk5 i (by omega) (by omega)
  rw [dif_neg h5]
  by_cases h6 : i.val < 448
  · rw [dif_pos h6]
    exact forward0_chunk6 i (by omega) (by omega)
  rw [dif_neg h6]
  by_cases h7 : i.val < 512
  · rw [dif_pos h7]
    exact forward0_chunk7 i (by omega) (by omega)
  rw [dif_neg h7]
  by_cases h8 : i.val < 576
  · rw [dif_pos h8]
    exact forward0_chunk8 i (by omega) (by omega)
  rw [dif_neg h8]
  by_cases h9 : i.val < 640
  · rw [dif_pos h9]
    exact forward0_chunk9 i (by omega) (by omega)
  rw [dif_neg h9]
  by_cases h10 : i.val < 704
  · rw [dif_pos h10]
    exact forward0_chunk10 i (by omega) (by omega)
  rw [dif_neg h10]
  by_cases h11 : i.val < 768
  · rw [dif_pos h11]
    exact forward0_chunk11 i (by omega) (by omega)
  rw [dif_neg h11]
  by_cases h12 : i.val < 832
  · rw [dif_pos h12]
    exact forward0_chunk12 i (by omega) (by omega)
  rw [dif_neg h12]
  exact forward0_chunk13 i (by omega) (by omega)

attribute [local irreducible] step1RowsChunk0 step1RowsChunk1 step1RowsChunk2 step1RowsChunk3 step1RowsChunk4 step1RowsChunk5 step1RowsChunk6 step1RowsChunk7 step1RowsChunk8 step1RowsChunk9 step1RowsChunk10 step1RowsChunk11 step1RowsChunk12
theorem step1Rows_chunk0 (i : Fin 808) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    step1Rows.get i = step1RowsChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem step1Rows_chunk1 (i : Fin 808) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    step1Rows.get i = step1RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk2 (i : Fin 808) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    step1Rows.get i = step1RowsChunk2.get ⟨i.val-128, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk3 (i : Fin 808) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    step1Rows.get i = step1RowsChunk3.get ⟨i.val-192, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk4 (i : Fin 808) (_hl : 256 ≤ i.val) (_hh : i.val < 320) :
    step1Rows.get i = step1RowsChunk4.get ⟨i.val-256, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk5 (i : Fin 808) (_hl : 320 ≤ i.val) (_hh : i.val < 384) :
    step1Rows.get i = step1RowsChunk5.get ⟨i.val-320, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk6 (i : Fin 808) (_hl : 384 ≤ i.val) (_hh : i.val < 448) :
    step1Rows.get i = step1RowsChunk6.get ⟨i.val-384, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk7 (i : Fin 808) (_hl : 448 ≤ i.val) (_hh : i.val < 512) :
    step1Rows.get i = step1RowsChunk7.get ⟨i.val-448, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk8 (i : Fin 808) (_hl : 512 ≤ i.val) (_hh : i.val < 576) :
    step1Rows.get i = step1RowsChunk8.get ⟨i.val-512, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk9 (i : Fin 808) (_hl : 576 ≤ i.val) (_hh : i.val < 640) :
    step1Rows.get i = step1RowsChunk9.get ⟨i.val-576, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk10 (i : Fin 808) (_hl : 640 ≤ i.val) (_hh : i.val < 704) :
    step1Rows.get i = step1RowsChunk10.get ⟨i.val-640, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk11 (i : Fin 808) (_hl : 704 ≤ i.val) (_hh : i.val < 768) :
    step1Rows.get i = step1RowsChunk11.get ⟨i.val-704, by omega⟩ := by
  unfold step1Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_chunk12 (i : Fin 808) (_hl : 768 ≤ i.val) (_hh : i.val < 808) :
    step1Rows.get i = step1RowsChunk12.get ⟨i.val-768, by omega⟩ := by
  unfold step1Rows
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step1Rows_get (i : Fin 808) : step1Rows.get i =
    if h0 : i.val < 64 then step1RowsChunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then step1RowsChunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then step1RowsChunk2.get ⟨i.val-128, by omega⟩ else
          if h3 : i.val < 256 then step1RowsChunk3.get ⟨i.val-192, by omega⟩ else
            if h4 : i.val < 320 then step1RowsChunk4.get ⟨i.val-256, by omega⟩ else
              if h5 : i.val < 384 then step1RowsChunk5.get ⟨i.val-320, by omega⟩ else
                if h6 : i.val < 448 then step1RowsChunk6.get ⟨i.val-384, by omega⟩ else
                  if h7 : i.val < 512 then step1RowsChunk7.get ⟨i.val-448, by omega⟩ else
                    if h8 : i.val < 576 then step1RowsChunk8.get ⟨i.val-512, by omega⟩ else
                      if h9 : i.val < 640 then step1RowsChunk9.get ⟨i.val-576, by omega⟩ else
                        if h10 : i.val < 704 then step1RowsChunk10.get ⟨i.val-640, by omega⟩ else
                          if h11 : i.val < 768 then step1RowsChunk11.get ⟨i.val-704, by omega⟩ else
                            step1RowsChunk12.get ⟨i.val-768, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact step1Rows_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact step1Rows_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact step1Rows_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 256
  · rw [dif_pos h3]
    exact step1Rows_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  by_cases h4 : i.val < 320
  · rw [dif_pos h4]
    exact step1Rows_chunk4 i (by omega) (by omega)
  rw [dif_neg h4]
  by_cases h5 : i.val < 384
  · rw [dif_pos h5]
    exact step1Rows_chunk5 i (by omega) (by omega)
  rw [dif_neg h5]
  by_cases h6 : i.val < 448
  · rw [dif_pos h6]
    exact step1Rows_chunk6 i (by omega) (by omega)
  rw [dif_neg h6]
  by_cases h7 : i.val < 512
  · rw [dif_pos h7]
    exact step1Rows_chunk7 i (by omega) (by omega)
  rw [dif_neg h7]
  by_cases h8 : i.val < 576
  · rw [dif_pos h8]
    exact step1Rows_chunk8 i (by omega) (by omega)
  rw [dif_neg h8]
  by_cases h9 : i.val < 640
  · rw [dif_pos h9]
    exact step1Rows_chunk9 i (by omega) (by omega)
  rw [dif_neg h9]
  by_cases h10 : i.val < 704
  · rw [dif_pos h10]
    exact step1Rows_chunk10 i (by omega) (by omega)
  rw [dif_neg h10]
  by_cases h11 : i.val < 768
  · rw [dif_pos h11]
    exact step1Rows_chunk11 i (by omega) (by omega)
  rw [dif_neg h11]
  exact step1Rows_chunk12 i (by omega) (by omega)

attribute [local irreducible] forward1Chunk0 forward1Chunk1 forward1Chunk2 forward1Chunk3 forward1Chunk4 forward1Chunk5 forward1Chunk6 forward1Chunk7 forward1Chunk8 forward1Chunk9 forward1Chunk10 forward1Chunk11 forward1Chunk12
theorem forward1_chunk0 (i : Fin 808) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    forward1.get i = forward1Chunk0.get ⟨i.val-0, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem forward1_chunk1 (i : Fin 808) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    forward1.get i = forward1Chunk1.get ⟨i.val-64, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk2 (i : Fin 808) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    forward1.get i = forward1Chunk2.get ⟨i.val-128, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk3 (i : Fin 808) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    forward1.get i = forward1Chunk3.get ⟨i.val-192, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk4 (i : Fin 808) (_hl : 256 ≤ i.val) (_hh : i.val < 320) :
    forward1.get i = forward1Chunk4.get ⟨i.val-256, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk5 (i : Fin 808) (_hl : 320 ≤ i.val) (_hh : i.val < 384) :
    forward1.get i = forward1Chunk5.get ⟨i.val-320, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk6 (i : Fin 808) (_hl : 384 ≤ i.val) (_hh : i.val < 448) :
    forward1.get i = forward1Chunk6.get ⟨i.val-384, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk7 (i : Fin 808) (_hl : 448 ≤ i.val) (_hh : i.val < 512) :
    forward1.get i = forward1Chunk7.get ⟨i.val-448, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk8 (i : Fin 808) (_hl : 512 ≤ i.val) (_hh : i.val < 576) :
    forward1.get i = forward1Chunk8.get ⟨i.val-512, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk9 (i : Fin 808) (_hl : 576 ≤ i.val) (_hh : i.val < 640) :
    forward1.get i = forward1Chunk9.get ⟨i.val-576, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk10 (i : Fin 808) (_hl : 640 ≤ i.val) (_hh : i.val < 704) :
    forward1.get i = forward1Chunk10.get ⟨i.val-640, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk11 (i : Fin 808) (_hl : 704 ≤ i.val) (_hh : i.val < 768) :
    forward1.get i = forward1Chunk11.get ⟨i.val-704, by omega⟩ := by
  unfold forward1
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_chunk12 (i : Fin 808) (_hl : 768 ≤ i.val) (_hh : i.val < 808) :
    forward1.get i = forward1Chunk12.get ⟨i.val-768, by omega⟩ := by
  unfold forward1
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward1_get (i : Fin 808) : forward1.get i =
    if h0 : i.val < 64 then forward1Chunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then forward1Chunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then forward1Chunk2.get ⟨i.val-128, by omega⟩ else
          if h3 : i.val < 256 then forward1Chunk3.get ⟨i.val-192, by omega⟩ else
            if h4 : i.val < 320 then forward1Chunk4.get ⟨i.val-256, by omega⟩ else
              if h5 : i.val < 384 then forward1Chunk5.get ⟨i.val-320, by omega⟩ else
                if h6 : i.val < 448 then forward1Chunk6.get ⟨i.val-384, by omega⟩ else
                  if h7 : i.val < 512 then forward1Chunk7.get ⟨i.val-448, by omega⟩ else
                    if h8 : i.val < 576 then forward1Chunk8.get ⟨i.val-512, by omega⟩ else
                      if h9 : i.val < 640 then forward1Chunk9.get ⟨i.val-576, by omega⟩ else
                        if h10 : i.val < 704 then forward1Chunk10.get ⟨i.val-640, by omega⟩ else
                          if h11 : i.val < 768 then forward1Chunk11.get ⟨i.val-704, by omega⟩ else
                            forward1Chunk12.get ⟨i.val-768, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact forward1_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact forward1_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact forward1_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 256
  · rw [dif_pos h3]
    exact forward1_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  by_cases h4 : i.val < 320
  · rw [dif_pos h4]
    exact forward1_chunk4 i (by omega) (by omega)
  rw [dif_neg h4]
  by_cases h5 : i.val < 384
  · rw [dif_pos h5]
    exact forward1_chunk5 i (by omega) (by omega)
  rw [dif_neg h5]
  by_cases h6 : i.val < 448
  · rw [dif_pos h6]
    exact forward1_chunk6 i (by omega) (by omega)
  rw [dif_neg h6]
  by_cases h7 : i.val < 512
  · rw [dif_pos h7]
    exact forward1_chunk7 i (by omega) (by omega)
  rw [dif_neg h7]
  by_cases h8 : i.val < 576
  · rw [dif_pos h8]
    exact forward1_chunk8 i (by omega) (by omega)
  rw [dif_neg h8]
  by_cases h9 : i.val < 640
  · rw [dif_pos h9]
    exact forward1_chunk9 i (by omega) (by omega)
  rw [dif_neg h9]
  by_cases h10 : i.val < 704
  · rw [dif_pos h10]
    exact forward1_chunk10 i (by omega) (by omega)
  rw [dif_neg h10]
  by_cases h11 : i.val < 768
  · rw [dif_pos h11]
    exact forward1_chunk11 i (by omega) (by omega)
  rw [dif_neg h11]
  exact forward1_chunk12 i (by omega) (by omega)

attribute [local irreducible] step2RowsChunk0 step2RowsChunk1 step2RowsChunk2 step2RowsChunk3 step2RowsChunk4 step2RowsChunk5 step2RowsChunk6 step2RowsChunk7 step2RowsChunk8 step2RowsChunk9
theorem step2Rows_chunk0 (i : Fin 608) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    step2Rows.get i = step2RowsChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem step2Rows_chunk1 (i : Fin 608) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    step2Rows.get i = step2RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk2 (i : Fin 608) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    step2Rows.get i = step2RowsChunk2.get ⟨i.val-128, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk3 (i : Fin 608) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    step2Rows.get i = step2RowsChunk3.get ⟨i.val-192, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk4 (i : Fin 608) (_hl : 256 ≤ i.val) (_hh : i.val < 320) :
    step2Rows.get i = step2RowsChunk4.get ⟨i.val-256, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk5 (i : Fin 608) (_hl : 320 ≤ i.val) (_hh : i.val < 384) :
    step2Rows.get i = step2RowsChunk5.get ⟨i.val-320, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk6 (i : Fin 608) (_hl : 384 ≤ i.val) (_hh : i.val < 448) :
    step2Rows.get i = step2RowsChunk6.get ⟨i.val-384, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk7 (i : Fin 608) (_hl : 448 ≤ i.val) (_hh : i.val < 512) :
    step2Rows.get i = step2RowsChunk7.get ⟨i.val-448, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk8 (i : Fin 608) (_hl : 512 ≤ i.val) (_hh : i.val < 576) :
    step2Rows.get i = step2RowsChunk8.get ⟨i.val-512, by omega⟩ := by
  unfold step2Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_chunk9 (i : Fin 608) (_hl : 576 ≤ i.val) (_hh : i.val < 608) :
    step2Rows.get i = step2RowsChunk9.get ⟨i.val-576, by omega⟩ := by
  unfold step2Rows
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step2Rows_get (i : Fin 608) : step2Rows.get i =
    if h0 : i.val < 64 then step2RowsChunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then step2RowsChunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then step2RowsChunk2.get ⟨i.val-128, by omega⟩ else
          if h3 : i.val < 256 then step2RowsChunk3.get ⟨i.val-192, by omega⟩ else
            if h4 : i.val < 320 then step2RowsChunk4.get ⟨i.val-256, by omega⟩ else
              if h5 : i.val < 384 then step2RowsChunk5.get ⟨i.val-320, by omega⟩ else
                if h6 : i.val < 448 then step2RowsChunk6.get ⟨i.val-384, by omega⟩ else
                  if h7 : i.val < 512 then step2RowsChunk7.get ⟨i.val-448, by omega⟩ else
                    if h8 : i.val < 576 then step2RowsChunk8.get ⟨i.val-512, by omega⟩ else
                      step2RowsChunk9.get ⟨i.val-576, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact step2Rows_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact step2Rows_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact step2Rows_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 256
  · rw [dif_pos h3]
    exact step2Rows_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  by_cases h4 : i.val < 320
  · rw [dif_pos h4]
    exact step2Rows_chunk4 i (by omega) (by omega)
  rw [dif_neg h4]
  by_cases h5 : i.val < 384
  · rw [dif_pos h5]
    exact step2Rows_chunk5 i (by omega) (by omega)
  rw [dif_neg h5]
  by_cases h6 : i.val < 448
  · rw [dif_pos h6]
    exact step2Rows_chunk6 i (by omega) (by omega)
  rw [dif_neg h6]
  by_cases h7 : i.val < 512
  · rw [dif_pos h7]
    exact step2Rows_chunk7 i (by omega) (by omega)
  rw [dif_neg h7]
  by_cases h8 : i.val < 576
  · rw [dif_pos h8]
    exact step2Rows_chunk8 i (by omega) (by omega)
  rw [dif_neg h8]
  exact step2Rows_chunk9 i (by omega) (by omega)

attribute [local irreducible] forward2Chunk0 forward2Chunk1 forward2Chunk2 forward2Chunk3 forward2Chunk4 forward2Chunk5 forward2Chunk6 forward2Chunk7 forward2Chunk8 forward2Chunk9
theorem forward2_chunk0 (i : Fin 608) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    forward2.get i = forward2Chunk0.get ⟨i.val-0, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem forward2_chunk1 (i : Fin 608) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    forward2.get i = forward2Chunk1.get ⟨i.val-64, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk2 (i : Fin 608) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    forward2.get i = forward2Chunk2.get ⟨i.val-128, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk3 (i : Fin 608) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    forward2.get i = forward2Chunk3.get ⟨i.val-192, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk4 (i : Fin 608) (_hl : 256 ≤ i.val) (_hh : i.val < 320) :
    forward2.get i = forward2Chunk4.get ⟨i.val-256, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk5 (i : Fin 608) (_hl : 320 ≤ i.val) (_hh : i.val < 384) :
    forward2.get i = forward2Chunk5.get ⟨i.val-320, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk6 (i : Fin 608) (_hl : 384 ≤ i.val) (_hh : i.val < 448) :
    forward2.get i = forward2Chunk6.get ⟨i.val-384, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk7 (i : Fin 608) (_hl : 448 ≤ i.val) (_hh : i.val < 512) :
    forward2.get i = forward2Chunk7.get ⟨i.val-448, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk8 (i : Fin 608) (_hl : 512 ≤ i.val) (_hh : i.val < 576) :
    forward2.get i = forward2Chunk8.get ⟨i.val-512, by omega⟩ := by
  unfold forward2
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_chunk9 (i : Fin 608) (_hl : 576 ≤ i.val) (_hh : i.val < 608) :
    forward2.get i = forward2Chunk9.get ⟨i.val-576, by omega⟩ := by
  unfold forward2
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward2_get (i : Fin 608) : forward2.get i =
    if h0 : i.val < 64 then forward2Chunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then forward2Chunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then forward2Chunk2.get ⟨i.val-128, by omega⟩ else
          if h3 : i.val < 256 then forward2Chunk3.get ⟨i.val-192, by omega⟩ else
            if h4 : i.val < 320 then forward2Chunk4.get ⟨i.val-256, by omega⟩ else
              if h5 : i.val < 384 then forward2Chunk5.get ⟨i.val-320, by omega⟩ else
                if h6 : i.val < 448 then forward2Chunk6.get ⟨i.val-384, by omega⟩ else
                  if h7 : i.val < 512 then forward2Chunk7.get ⟨i.val-448, by omega⟩ else
                    if h8 : i.val < 576 then forward2Chunk8.get ⟨i.val-512, by omega⟩ else
                      forward2Chunk9.get ⟨i.val-576, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact forward2_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact forward2_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact forward2_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 256
  · rw [dif_pos h3]
    exact forward2_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  by_cases h4 : i.val < 320
  · rw [dif_pos h4]
    exact forward2_chunk4 i (by omega) (by omega)
  rw [dif_neg h4]
  by_cases h5 : i.val < 384
  · rw [dif_pos h5]
    exact forward2_chunk5 i (by omega) (by omega)
  rw [dif_neg h5]
  by_cases h6 : i.val < 448
  · rw [dif_pos h6]
    exact forward2_chunk6 i (by omega) (by omega)
  rw [dif_neg h6]
  by_cases h7 : i.val < 512
  · rw [dif_pos h7]
    exact forward2_chunk7 i (by omega) (by omega)
  rw [dif_neg h7]
  by_cases h8 : i.val < 576
  · rw [dif_pos h8]
    exact forward2_chunk8 i (by omega) (by omega)
  rw [dif_neg h8]
  exact forward2_chunk9 i (by omega) (by omega)

attribute [local irreducible] step3RowsChunk0 step3RowsChunk1 step3RowsChunk2 step3RowsChunk3
theorem step3Rows_chunk0 (i : Fin 256) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    step3Rows.get i = step3RowsChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold step3Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem step3Rows_chunk1 (i : Fin 256) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    step3Rows.get i = step3RowsChunk1.get ⟨i.val-64, by omega⟩ := by
  unfold step3Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step3Rows_chunk2 (i : Fin 256) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    step3Rows.get i = step3RowsChunk2.get ⟨i.val-128, by omega⟩ := by
  unfold step3Rows
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step3Rows_chunk3 (i : Fin 256) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    step3Rows.get i = step3RowsChunk3.get ⟨i.val-192, by omega⟩ := by
  unfold step3Rows
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem step3Rows_get (i : Fin 256) : step3Rows.get i =
    if h0 : i.val < 64 then step3RowsChunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then step3RowsChunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then step3RowsChunk2.get ⟨i.val-128, by omega⟩ else
          step3RowsChunk3.get ⟨i.val-192, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact step3Rows_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact step3Rows_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact step3Rows_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  exact step3Rows_chunk3 i (by omega) (by omega)

attribute [local irreducible] forward3Chunk0 forward3Chunk1 forward3Chunk2 forward3Chunk3
theorem forward3_chunk0 (i : Fin 256) (_hl : 0 ≤ i.val) (_hh : i.val < 64) :
    forward3.get i = forward3Chunk0.get ⟨i.val-0, by omega⟩ := by
  unfold forward3
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem forward3_chunk1 (i : Fin 256) (_hl : 64 ≤ i.val) (_hh : i.val < 128) :
    forward3.get i = forward3Chunk1.get ⟨i.val-64, by omega⟩ := by
  unfold forward3
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward3_chunk2 (i : Fin 256) (_hl : 128 ≤ i.val) (_hh : i.val < 192) :
    forward3.get i = forward3Chunk2.get ⟨i.val-128, by omega⟩ := by
  unfold forward3
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward3_chunk3 (i : Fin 256) (_hl : 192 ≤ i.val) (_hh : i.val < 256) :
    forward3.get i = forward3Chunk3.get ⟨i.val-192, by omega⟩ := by
  unfold forward3
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem forward3_get (i : Fin 256) : forward3.get i =
    if h0 : i.val < 64 then forward3Chunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 128 then forward3Chunk1.get ⟨i.val-64, by omega⟩ else
        if h2 : i.val < 192 then forward3Chunk2.get ⟨i.val-128, by omega⟩ else
          forward3Chunk3.get ⟨i.val-192, by omega⟩ := by
  by_cases h0 : i.val < 64
  · rw [dif_pos h0]
    exact forward3_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 128
  · rw [dif_pos h1]
    exact forward3_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 192
  · rw [dif_pos h2]
    exact forward3_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  exact forward3_chunk3 i (by omega) (by omega)

attribute [local irreducible] reverse0SparseChunk0 reverse0SparseChunk1 reverse0SparseChunk2 reverse0SparseChunk3 reverse0SparseChunk4 reverse0SparseChunk5 reverse0SparseChunk6
theorem reverse0Sparse_chunk0 (i : Fin 101) (_hl : 0 ≤ i.val) (_hh : i.val < 16) :
    reverse0Sparse.get i = reverse0SparseChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold reverse0Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem reverse0Sparse_chunk1 (i : Fin 101) (_hl : 16 ≤ i.val) (_hh : i.val < 32) :
    reverse0Sparse.get i = reverse0SparseChunk1.get ⟨i.val-16, by omega⟩ := by
  unfold reverse0Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse0Sparse_chunk2 (i : Fin 101) (_hl : 32 ≤ i.val) (_hh : i.val < 48) :
    reverse0Sparse.get i = reverse0SparseChunk2.get ⟨i.val-32, by omega⟩ := by
  unfold reverse0Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse0Sparse_chunk3 (i : Fin 101) (_hl : 48 ≤ i.val) (_hh : i.val < 64) :
    reverse0Sparse.get i = reverse0SparseChunk3.get ⟨i.val-48, by omega⟩ := by
  unfold reverse0Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse0Sparse_chunk4 (i : Fin 101) (_hl : 64 ≤ i.val) (_hh : i.val < 80) :
    reverse0Sparse.get i = reverse0SparseChunk4.get ⟨i.val-64, by omega⟩ := by
  unfold reverse0Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse0Sparse_chunk5 (i : Fin 101) (_hl : 80 ≤ i.val) (_hh : i.val < 96) :
    reverse0Sparse.get i = reverse0SparseChunk5.get ⟨i.val-80, by omega⟩ := by
  unfold reverse0Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse0Sparse_chunk6 (i : Fin 101) (_hl : 96 ≤ i.val) (_hh : i.val < 101) :
    reverse0Sparse.get i = reverse0SparseChunk6.get ⟨i.val-96, by omega⟩ := by
  unfold reverse0Sparse
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse0Sparse_get (i : Fin 101) : reverse0Sparse.get i =
    if h0 : i.val < 16 then reverse0SparseChunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 32 then reverse0SparseChunk1.get ⟨i.val-16, by omega⟩ else
        if h2 : i.val < 48 then reverse0SparseChunk2.get ⟨i.val-32, by omega⟩ else
          if h3 : i.val < 64 then reverse0SparseChunk3.get ⟨i.val-48, by omega⟩ else
            if h4 : i.val < 80 then reverse0SparseChunk4.get ⟨i.val-64, by omega⟩ else
              if h5 : i.val < 96 then reverse0SparseChunk5.get ⟨i.val-80, by omega⟩ else
                reverse0SparseChunk6.get ⟨i.val-96, by omega⟩ := by
  by_cases h0 : i.val < 16
  · rw [dif_pos h0]
    exact reverse0Sparse_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 32
  · rw [dif_pos h1]
    exact reverse0Sparse_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 48
  · rw [dif_pos h2]
    exact reverse0Sparse_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 64
  · rw [dif_pos h3]
    exact reverse0Sparse_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  by_cases h4 : i.val < 80
  · rw [dif_pos h4]
    exact reverse0Sparse_chunk4 i (by omega) (by omega)
  rw [dif_neg h4]
  by_cases h5 : i.val < 96
  · rw [dif_pos h5]
    exact reverse0Sparse_chunk5 i (by omega) (by omega)
  rw [dif_neg h5]
  exact reverse0Sparse_chunk6 i (by omega) (by omega)

attribute [local irreducible] reverse1SparseChunk0 reverse1SparseChunk1 reverse1SparseChunk2 reverse1SparseChunk3 reverse1SparseChunk4
theorem reverse1Sparse_chunk0 (i : Fin 76) (_hl : 0 ≤ i.val) (_hh : i.val < 16) :
    reverse1Sparse.get i = reverse1SparseChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold reverse1Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem reverse1Sparse_chunk1 (i : Fin 76) (_hl : 16 ≤ i.val) (_hh : i.val < 32) :
    reverse1Sparse.get i = reverse1SparseChunk1.get ⟨i.val-16, by omega⟩ := by
  unfold reverse1Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse1Sparse_chunk2 (i : Fin 76) (_hl : 32 ≤ i.val) (_hh : i.val < 48) :
    reverse1Sparse.get i = reverse1SparseChunk2.get ⟨i.val-32, by omega⟩ := by
  unfold reverse1Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse1Sparse_chunk3 (i : Fin 76) (_hl : 48 ≤ i.val) (_hh : i.val < 64) :
    reverse1Sparse.get i = reverse1SparseChunk3.get ⟨i.val-48, by omega⟩ := by
  unfold reverse1Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse1Sparse_chunk4 (i : Fin 76) (_hl : 64 ≤ i.val) (_hh : i.val < 76) :
    reverse1Sparse.get i = reverse1SparseChunk4.get ⟨i.val-64, by omega⟩ := by
  unfold reverse1Sparse
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse1Sparse_get (i : Fin 76) : reverse1Sparse.get i =
    if h0 : i.val < 16 then reverse1SparseChunk0.get ⟨i.val-0, by omega⟩ else
      if h1 : i.val < 32 then reverse1SparseChunk1.get ⟨i.val-16, by omega⟩ else
        if h2 : i.val < 48 then reverse1SparseChunk2.get ⟨i.val-32, by omega⟩ else
          if h3 : i.val < 64 then reverse1SparseChunk3.get ⟨i.val-48, by omega⟩ else
            reverse1SparseChunk4.get ⟨i.val-64, by omega⟩ := by
  by_cases h0 : i.val < 16
  · rw [dif_pos h0]
    exact reverse1Sparse_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  by_cases h1 : i.val < 32
  · rw [dif_pos h1]
    exact reverse1Sparse_chunk1 i (by omega) (by omega)
  rw [dif_neg h1]
  by_cases h2 : i.val < 48
  · rw [dif_pos h2]
    exact reverse1Sparse_chunk2 i (by omega) (by omega)
  rw [dif_neg h2]
  by_cases h3 : i.val < 64
  · rw [dif_pos h3]
    exact reverse1Sparse_chunk3 i (by omega) (by omega)
  rw [dif_neg h3]
  exact reverse1Sparse_chunk4 i (by omega) (by omega)

attribute [local irreducible] reverse2SparseChunk0 reverse2SparseChunk1
theorem reverse2Sparse_chunk0 (i : Fin 32) (_hl : 0 ≤ i.val) (_hh : i.val < 16) :
    reverse2Sparse.get i = reverse2SparseChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold reverse2Sparse
  rw [get_append_left (h := by change i.val < _; omega)]
  rfl

theorem reverse2Sparse_chunk1 (i : Fin 32) (_hl : 16 ≤ i.val) (_hh : i.val < 32) :
    reverse2Sparse.get i = reverse2SparseChunk1.get ⟨i.val-16, by omega⟩ := by
  unfold reverse2Sparse
  rw [get_append_right (h := by change _ ≤ i.val; omega)]

theorem reverse2Sparse_get (i : Fin 32) : reverse2Sparse.get i =
    if h0 : i.val < 16 then reverse2SparseChunk0.get ⟨i.val-0, by omega⟩ else
      reverse2SparseChunk1.get ⟨i.val-16, by omega⟩ := by
  by_cases h0 : i.val < 16
  · rw [dif_pos h0]
    exact reverse2Sparse_chunk0 i (by omega) (by omega)
  rw [dif_neg h0]
  exact reverse2Sparse_chunk1 i (by omega) (by omega)

attribute [local irreducible] reverse3SparseChunk0
theorem reverse3Sparse_chunk0 (i : Fin 4) (_hl : 0 ≤ i.val) (_hh : i.val < 4) :
    reverse3Sparse.get i = reverse3SparseChunk0.get ⟨i.val-0, by omega⟩ := by
  unfold reverse3Sparse
  rfl

theorem reverse3Sparse_get (i : Fin 4) : reverse3Sparse.get i =
    reverse3SparseChunk0.get ⟨i.val-0, by omega⟩ := by
  exact reverse3Sparse_chunk0 i (by omega) (by omega)

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
