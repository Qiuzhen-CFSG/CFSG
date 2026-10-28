module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Data
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Candidates

/-!
# Interpretation of the HS projector witness data

The auxiliary rows decode to H = A+B+omega² I and Q = I+uv. Only the two
independently produced generator re-encoding equations remain as premises.
The vector encodings are checked here against the shared null vectors.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
open Packed
set_option Elab.async false

private theorem uPlanes_interleave : interleave 896 uPlanes = nullColumnPacked := by
  decide +kernel
private theorem vPlanes_interleave : interleave 896 vPlanes = nullRowPacked := by
  decide +kernel

theorem uPlanes_decode (i : Fin 896) : decode uPlanes i.val = nullColumn i := by
  rw [← entry_interleave 896 uPlanes i, uPlanes_interleave]
  rfl

theorem vPlanes_decode (i : Fin 896) : decode vPlanes i.val = nullRow i := by
  rw [← entry_interleave 896 vPlanes i, vPlanes_interleave]
  rfl

private def hFormula (i : ℕ) (a b : Row) : Row :=
  Base.addRow (Base.addRow a b) (2 ^ i, 2 ^ i)

set_option maxRecDepth 4096 in
private theorem hRows_checked : checkZip hFormula generatorRowsA generatorRowsB hRows 0 = true := by
  decide +kernel

theorem hRows_get (i : Fin 896) : hRows.getD i.val (0, 0) =
    Base.addRow (Base.addRow (generatorRowsA.getD i.val (0, 0))
      (generatorRowsB.getD i.val (0, 0))) (2 ^ i.val, 2 ^ i.val) := by
  simpa only [Nat.zero_add, hFormula] using checkZip_get hFormula generatorRowsA generatorRowsB hRows 0 hRows_checked i.val
    (by simpa only [generatorRowsA_length] using i.isLt)

private def qFormula (i : ℕ) : Row := Base.addRow (unitRow i) (scaleRow uPlanes i vPlanes)

set_option maxRecDepth 4096 in
private theorem qRows_checked : checkFormula qFormula qRows 0 = true := by decide +kernel

theorem qRows_get (i : Fin 896) : qRows.getD i.val (0, 0) =
    Base.addRow (unitRow i.val) (scaleRow uPlanes i.val vPlanes) := by
  simpa only [Nat.zero_add, qFormula] using checkFormula_get qFormula qRows 0 qRows_checked i.val (by simpa only [qRows_length] using i.isLt)

theorem eval_hRows
    (hA : Packed.eval 896 generatorRowsA = matrixA)
    (hB : Packed.eval 896 generatorRowsB = matrixB) : eval 896 hRows = singular := by
  rw [singular, ← hA, ← hB]
  funext i j
  change decode (hRows.getD i.val (0, 0)) j.val = _
  rw [hRows_get, decode_add, decode_add, decode_diagonal]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.val_inj, eval]

theorem eval_qRows : eval 896 qRows = 1 + Matrix.vecMulVec nullColumn nullRow := by
  funext i j
  change decode (qRows.getD i.val (0, 0)) j.val = _
  rw [qRows_get, decode_add, decode_unitRow, decode_scaleRow, uPlanes_decode, vPlanes_decode]
  simp only [Fin.val_inj, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply]

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
