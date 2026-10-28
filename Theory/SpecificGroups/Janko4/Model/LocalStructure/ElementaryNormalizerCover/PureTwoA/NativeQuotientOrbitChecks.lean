module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeQuotientOrbitData

/-! # Checked conjugation edges for the native quotient class

The earlier-parent tree and sorted matrix codes certify 1155 distinct
conjugates. All checks use Lean kernel reduction on 12-dimensional matrices.
See `NativeQuotientOrbitData` for the native source marking.
-/

public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeQuotientOrbit
open Cardinality.LocalInvolutionCensus.QuotientCensus
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

private theorem block0 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (0 + i.val)) := by decide +kernel

private theorem block1 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (64 + i.val)) := by decide +kernel

private theorem block2 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (128 + i.val)) := by decide +kernel

private theorem block3 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (192 + i.val)) := by decide +kernel

private theorem block4 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (256 + i.val)) := by decide +kernel

private theorem block5 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (320 + i.val)) := by decide +kernel

private theorem block6 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (384 + i.val)) := by decide +kernel

private theorem block7 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (448 + i.val)) := by decide +kernel

private theorem block8 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (512 + i.val)) := by decide +kernel

private theorem block9 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (576 + i.val)) := by decide +kernel

private theorem block10 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (640 + i.val)) := by decide +kernel

private theorem block11 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (704 + i.val)) := by decide +kernel

private theorem block12 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (768 + i.val)) := by decide +kernel

private theorem block13 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (832 + i.val)) := by decide +kernel

private theorem block14 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (896 + i.val)) := by decide +kernel

private theorem block15 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (960 + i.val)) := by decide +kernel

private theorem block16 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (1024 + i.val)) := by decide +kernel

private theorem block17 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (1088 + i.val)) := by decide +kernel

private theorem block18 : ∀ i : Fin 64,
    EdgeCheck (Fin.ofNat 1155 (1152 + i.val)) := by decide +kernel

theorem edges_checked (i : Fin 1155) : EdgeCheck i := by
  have hh (b : Fin 19) (r : Fin 64) : EdgeCheck (Fin.ofNat 1155 (64*b.val+r.val)) := by
    fin_cases b
    · exact block0 r
    · exact block1 r
    · exact block2 r
    · exact block3 r
    · exact block4 r
    · exact block5 r
    · exact block6 r
    · exact block7 r
    · exact block8 r
    · exact block9 r
    · exact block10 r
    · exact block11 r
    · exact block12 r
    · exact block13 r
    · exact block14 r
    · exact block15 r
    · exact block16 r
    · exact block17 r
    · exact block18 r
  have hi := hh ⟨i.val/64, by omega⟩ ⟨i.val%64, Nat.mod_lt _ (by decide)⟩
  have he : 64*(i.val/64)+i.val%64 = i.val := by omega
  simpa only [he, Fin.ofNat_val_eq_self] using hi

theorem sorted_checked : ∀ i : Fin 1154,
    (orbitCode (sorted i.castSucc)).toNat <
      (orbitCode (sorted i.succ)).toNat := by decide +kernel

theorem root_checked : orbitCode 0 = code (markedIndex 3) := by decide +kernel

theorem generators_checked (i : Fin 4) :
    (basic i).val.val = decode (generatorCode i) := by
  fin_cases i <;> decide +kernel
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeQuotientOrbit
