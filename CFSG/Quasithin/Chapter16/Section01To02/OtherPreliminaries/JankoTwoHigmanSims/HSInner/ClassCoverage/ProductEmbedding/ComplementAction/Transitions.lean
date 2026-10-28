module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementAction.Checks
import Mathlib.Tactic.FinCases

/-!
# Exhaustive generator transitions for the HS complement

All 5760 right products, each at all 100 points, are checked in the kernel.
Twelve bounded batches keep each reduction small; `value_step` reassembles
these checks for arbitrary row, letter, and point indices.
Source: Aschbacher–Smith 16.1.5(10), p.1172; GLS3 Table 5.3m.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementCertificate
open Theory.GroupTheory Sporadic.LeechRelated.HS
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

private def blockRow (b : Fin 12) (i : Fin 120) : Fin 1440 :=
  ⟨120 * b.val + i.val, by omega⟩

private def stepChunk (b : Fin 12) : Bool :=
  checkFin (fun i : Fin 120 => checkFin (fun s : Fin 4 =>
    checkFin (fun p : Fin 100 => decide
      (value (next (blockRow b i) s) p = value (blockRow b i) (letterValue s p)))))

private theorem chunk_0 : stepChunk 0 = true := by
  decide +kernel

private theorem chunk_1 : stepChunk 1 = true := by
  decide +kernel

private theorem chunk_2 : stepChunk 2 = true := by
  decide +kernel

private theorem chunk_3 : stepChunk 3 = true := by
  decide +kernel

private theorem chunk_4 : stepChunk 4 = true := by
  decide +kernel

private theorem chunk_5 : stepChunk 5 = true := by
  decide +kernel

private theorem chunk_6 : stepChunk 6 = true := by
  decide +kernel

private theorem chunk_7 : stepChunk 7 = true := by
  decide +kernel

private theorem chunk_8 : stepChunk 8 = true := by
  decide +kernel

private theorem chunk_9 : stepChunk 9 = true := by
  decide +kernel

private theorem chunk_10 : stepChunk 10 = true := by
  decide +kernel

private theorem chunk_11 : stepChunk 11 = true := by
  decide +kernel

private theorem stepChunk_checked (b : Fin 12) : stepChunk b = true := by
  fin_cases b
  · exact chunk_0
  · exact chunk_1
  · exact chunk_2
  · exact chunk_3
  · exact chunk_4
  · exact chunk_5
  · exact chunk_6
  · exact chunk_7
  · exact chunk_8
  · exact chunk_9
  · exact chunk_10
  · exact chunk_11

theorem value_step (i : Fin 1440) (s : Fin 4) (p : Fin 100) :
    value (next i s) p = value i (letterValue s p) := by
  let b : Fin 12 := ⟨i.val / 120, by omega⟩
  let r : Fin 120 := ⟨i.val % 120, Nat.mod_lt _ (by decide)⟩
  have hr : blockRow b r = i := by
    apply Fin.ext
    dsimp [blockRow, b, r]
    omega
  have h := of_decide_eq_true
    (checkedAt (checkedAt (checkedAt (stepChunk_checked b) r) s) p)
  change value (next (blockRow b r) s) p = value (blockRow b r) (letterValue s p) at h
  simpa only [hr] using h

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementCertificate
