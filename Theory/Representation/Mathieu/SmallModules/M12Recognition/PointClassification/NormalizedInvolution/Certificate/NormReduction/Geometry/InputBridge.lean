module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Tables
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Inputs

/-!
# Identification of the packed shared inputs

Whole input blocks are checked against packed copies. A generic extraction
lemma then identifies each literal array entry with its packed field.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry

open Inputs

def unpack (width : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n+1, c => c % 2^width :: unpack width n (c >>> width)

theorem unpack_get (width n c i : ℕ) (hi : i < n) :
    (unpack width n c)[i]! = (c >>> (width*i)) % 2^width := by
  induction n generalizing c i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [unpack]
    | succ i =>
      rw [unpack, List.getElem!_cons_succ, ih _ _ (by omega)]
      rw [← Nat.shiftRight_add]
      simp only [Nat.mul_succ, Nat.add_comm]


theorem packed_lookup (table : Array (Array ℕ)) (block : ℕ → ℕ)
    (width count n : ℕ) (hn : n ≤ count*128)
    (hb : ∀ b : Fin count, (table[b.val]!).toList =
      unpack width (min 128 (n-b.val*128)) (block b.val))
    (i : Fin n) :
    tableEntry table i.val = (block (i.val/128) >>> (width*(i.val%128))) % 2^width := by
  rw [tableEntry, ← Array.getElem!_toList,
    hb ⟨i.val/128, by omega⟩, unpack_get]
  change i.val % 128 < min 128 (n - i.val / 128 * 128)
  have hi := i.isLt
  omega

theorem word_blocks : ∀ b : Fin 62, (wordCodes[b.val]!).toList =
    unpack 32 (min 128 (7920-b.val*128)) (wordBlock b.val) := by
  decide +kernel

theorem wordCode_eq (i : Fin 7920) : wordCode i.val = tableEntry wordCodes i.val := by
  exact (packed_lookup wordCodes wordBlock 32 62 7920
    (by decide) word_blocks i).symm

theorem seed_blocks : ∀ b : Fin 60, (seedCodes[b.val]!).toList =
    unpack 143 (min 128 (7620-b.val*128)) (seedBlock b.val) := by
  decide +kernel

theorem seedCode_eq (i : Fin 7620) : seedCode i.val = tableEntry seedCodes i.val := by
  exact (packed_lookup seedCodes seedBlock 143 60 7620
    (by decide) seed_blocks i).symm

theorem translate_blocks : ∀ b : Fin 60, (translateCodes[b.val]!).toList =
    unpack 26 (min 128 (7620-b.val*128)) (translateBlock b.val) := by
  decide +kernel

theorem translateCode_eq (i : Fin 7620) : translateCode i.val = tableEntry translateCodes i.val := by
  exact (packed_lookup translateCodes translateBlock 26 60 7620
    (by decide) translate_blocks i).symm

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry
