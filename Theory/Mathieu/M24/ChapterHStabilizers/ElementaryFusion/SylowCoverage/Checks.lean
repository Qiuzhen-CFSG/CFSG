module
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage.Data

/-!
# Kernel checks for the Sylow commutation graph and candidate words

Three base images suffice to reject a square-one element outside the vertex
list, or a noncommuting pair. Candidate transitions toggle generator bits.
All checks use the certified native enumeration; no normality is assumed.
Source: Aschbacher–Smith H.14.1(1,5), printed pp.396–397.
-/
@[expose] public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open M24LocalGeometry SylowNormalizer.OrderEnumeration
set_option maxRecDepth 10000

theorem vertexPoint_spec : ∀ v x, vertexPoint v x = point (vertexIndex v) x := by
  decide +kernel

theorem square_rejection : ∀ i : Fin 1024,
    vertexIndex (vertexCode i) = i ∨
    point i (point i 0) ≠ 0 ∨ point i (point i 1) ≠ 1 ∨ point i (point i 5) ≠ 5 := by
  decide +kernel

private def GoodRow (v : Fin 192) : Prop := ∀ w : Fin 192,
    compatible v w = true ∨
    vertexPoint v (vertexPoint w 0) ≠ vertexPoint w (vertexPoint v 0) ∨
    vertexPoint v (vertexPoint w 1) ≠ vertexPoint w (vertexPoint v 1) ∨
    vertexPoint v (vertexPoint w 5) ≠ vertexPoint w (vertexPoint v 5)

private theorem graph_block_00 : ∀ a : Fin 8,
    GoodRow ⟨8 * 0 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_01 : ∀ a : Fin 8,
    GoodRow ⟨8 * 1 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_02 : ∀ a : Fin 8,
    GoodRow ⟨8 * 2 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_03 : ∀ a : Fin 8,
    GoodRow ⟨8 * 3 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_04 : ∀ a : Fin 8,
    GoodRow ⟨8 * 4 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_05 : ∀ a : Fin 8,
    GoodRow ⟨8 * 5 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_06 : ∀ a : Fin 8,
    GoodRow ⟨8 * 6 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_07 : ∀ a : Fin 8,
    GoodRow ⟨8 * 7 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_08 : ∀ a : Fin 8,
    GoodRow ⟨8 * 8 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_09 : ∀ a : Fin 8,
    GoodRow ⟨8 * 9 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_10 : ∀ a : Fin 8,
    GoodRow ⟨8 * 10 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_11 : ∀ a : Fin 8,
    GoodRow ⟨8 * 11 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_12 : ∀ a : Fin 8,
    GoodRow ⟨8 * 12 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_13 : ∀ a : Fin 8,
    GoodRow ⟨8 * 13 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_14 : ∀ a : Fin 8,
    GoodRow ⟨8 * 14 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_15 : ∀ a : Fin 8,
    GoodRow ⟨8 * 15 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_16 : ∀ a : Fin 8,
    GoodRow ⟨8 * 16 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_17 : ∀ a : Fin 8,
    GoodRow ⟨8 * 17 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_18 : ∀ a : Fin 8,
    GoodRow ⟨8 * 18 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_19 : ∀ a : Fin 8,
    GoodRow ⟨8 * 19 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_20 : ∀ a : Fin 8,
    GoodRow ⟨8 * 20 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_21 : ∀ a : Fin 8,
    GoodRow ⟨8 * 21 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_22 : ∀ a : Fin 8,
    GoodRow ⟨8 * 22 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

private theorem graph_block_23 : ∀ a : Fin 8,
    GoodRow ⟨8 * 23 + a.val, by omega⟩ := by
  unfold GoodRow
  decide +kernel

theorem compatible_check (v w : Fin 192)
    (hc : vertexPoint v (vertexPoint w 0) = vertexPoint w (vertexPoint v 0) ∧
      vertexPoint v (vertexPoint w 1) = vertexPoint w (vertexPoint v 1) ∧
      vertexPoint v (vertexPoint w 5) = vertexPoint w (vertexPoint v 5)) :
    compatible v w = true := by
  have blocks : ∀ (b : Fin 24) (a : Fin 8), GoodRow ⟨8 * b.val + a.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact graph_block_00
    · exact graph_block_01
    · exact graph_block_02
    · exact graph_block_03
    · exact graph_block_04
    · exact graph_block_05
    · exact graph_block_06
    · exact graph_block_07
    · exact graph_block_08
    · exact graph_block_09
    · exact graph_block_10
    · exact graph_block_11
    · exact graph_block_12
    · exact graph_block_13
    · exact graph_block_14
    · exact graph_block_15
    · exact graph_block_16
    · exact graph_block_17
    · exact graph_block_18
    · exact graph_block_19
    · exact graph_block_20
    · exact graph_block_21
    · exact graph_block_22
    · exact graph_block_23
  have h := blocks ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  have he : (⟨8 * (v.val / 8) + v.val % 8, by omega⟩ : Fin 192) = v := by
    apply Fin.ext
    change 8 * (v.val / 8) + v.val % 8 = v.val
    omega
  rw [he] at h
  rcases h w with h | h | h | h
  · exact h
  · exact (h hc.1).elim
  · exact (h hc.2.1).elim
  · exact (h hc.2.2).elim

def toggle (a : Fin 5) (j : Fin 32) : Fin 32 :=
  ⟨(j.val ^^^ 2 ^ a.val) % 32, Nat.mod_lt _ (by decide)⟩

def generatorVertex (k : Fin 4) (a : Fin 5) : Fin 192 :=
  vertexCode (smallGeneratorIndex k a)

theorem generatorVertex_spec : ∀ k a,
    vertexIndex (generatorVertex k a) = smallGeneratorIndex k a := by decide +kernel

theorem small_step_check : ∀ (k : Fin 4) (a : Fin 5) (j : Fin 32) (b : Fin 3),
    vertexPoint (generatorVertex k a)
        (vertexPoint (smallRow k j) (EvenCatalogue.NormalizerOvergroupsProof.basePoint b)) =
      vertexPoint (smallRow k (toggle a j))
        (EvenCatalogue.NormalizerOvergroupsProof.basePoint b) := by
  decide +kernel

theorem small_square_check : ∀ (k : Fin 4) (a : Fin 5) (b : Fin 3),
    vertexPoint (generatorVertex k a)
        (vertexPoint (generatorVertex k a) (EvenCatalogue.NormalizerOvergroupsProof.basePoint b)) =
      EvenCatalogue.NormalizerOvergroupsProof.basePoint b := by decide +kernel

theorem small_zero_check : ∀ k, vertexIndex (smallRow k 0) = 0 := by decide +kernel

def lowerMask (j : Fin 32) : Fin 32 :=
  ⟨(j.val - 2 ^ Nat.log2 j.val) % 32, Nat.mod_lt _ (by decide)⟩

def lastBit (j : Fin 32) : Fin 5 :=
  ⟨Nat.log2 j.val % 5, Nat.mod_lt _ (by decide)⟩

theorem lower_check : ∀ j : Fin 32, j ≠ 0 →
    lowerMask j < j ∧ toggle (lastBit j) (lowerMask j) = j := by decide +kernel

theorem small_mask_check : ∀ (k : Fin 4) (v : Fin 192),
    (largeMask k.castSucc.castSucc).testBit v.val = true →
    vertexIndex v = vertexIndex (smallRow k ⟨(wordCode k.castSucc.castSucc v).val % 32,
      Nat.mod_lt _ (by decide)⟩) := by decide +kernel

theorem even_mask_check : ∀ (k : Fin 2) (v : Fin 192),
    (largeMask ⟨4 + k.val, by omega⟩).testBit v.val = true →
    vertexIndex v = EvenCatalogue.NormalizerOvergroupsProof.elementIndex
      (EvenCatalogue.NormalizerOvergroupsProof.rowCode (if k = 0 then 20 else 21)
        (wordCode ⟨4 + k.val, by omega⟩ v)) := by decide +kernel

end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
