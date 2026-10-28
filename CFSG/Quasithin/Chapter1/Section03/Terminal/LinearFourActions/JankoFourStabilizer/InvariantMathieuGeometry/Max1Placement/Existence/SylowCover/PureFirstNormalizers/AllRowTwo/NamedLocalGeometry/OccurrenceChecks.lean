module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.OccurrenceData

/-!
# Checked native F-occurrence tree and separation

Each bounded block checks explicit noncommuting witnesses, avoiding searches
through pairs of generators. Together the blocks distinguish all 330 actual
candidates. The tree checks retain the full thirteen-bit action and the same
ambient word. Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489, and
the native ATLAS action data documented in `OccurrenceData`.
-/

public section
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.OccurrenceTable
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
set_option Elab.async false

theorem edges : ∀ i : Fin 330, i ≠ 0 → parent i < i ∧
    word i = word (parent i) ++ [step i] ∧
    ∀ j : Fin 7, fastAction (step i) (label (parent i) j).val = (label i j).val := by
  decide +kernel

theorem root_labels : ∀ j : Fin 7,
    label 0 j = seedCoordinate ⟨2^j.val % 128, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

theorem central_labels : ∀ i : Fin 330, label i 0 = 1 := by decide +kernel

theorem root_word : word 0 = [] := by decide +kernel

private theorem block0 : allBlock pairRow 3 0 = true := by decide +kernel
private theorem block1 : allBlock pairRow 3 8 = true := by decide +kernel
private theorem block2 : allBlock pairRow 3 16 = true := by decide +kernel
private theorem block3 : allBlock pairRow 3 24 = true := by decide +kernel
private theorem block4 : allBlock pairRow 3 32 = true := by decide +kernel
private theorem block5 : allBlock pairRow 3 40 = true := by decide +kernel
private theorem block6 : allBlock pairRow 3 48 = true := by decide +kernel
private theorem block7 : allBlock pairRow 3 56 = true := by decide +kernel
private theorem block8 : allBlock pairRow 3 64 = true := by decide +kernel
private theorem block9 : allBlock pairRow 3 72 = true := by decide +kernel
private theorem block10 : allBlock pairRow 3 80 = true := by decide +kernel
private theorem block11 : allBlock pairRow 3 88 = true := by decide +kernel
private theorem block12 : allBlock pairRow 3 96 = true := by decide +kernel
private theorem block13 : allBlock pairRow 3 104 = true := by decide +kernel
private theorem block14 : allBlock pairRow 3 112 = true := by decide +kernel
private theorem block15 : allBlock pairRow 3 120 = true := by decide +kernel
private theorem block16 : allBlock pairRow 3 128 = true := by decide +kernel
private theorem block17 : allBlock pairRow 3 136 = true := by decide +kernel
private theorem block18 : allBlock pairRow 3 144 = true := by decide +kernel
private theorem block19 : allBlock pairRow 3 152 = true := by decide +kernel
private theorem block20 : allBlock pairRow 3 160 = true := by decide +kernel
private theorem block21 : allBlock pairRow 3 168 = true := by decide +kernel
private theorem block22 : allBlock pairRow 3 176 = true := by decide +kernel
private theorem block23 : allBlock pairRow 3 184 = true := by decide +kernel
private theorem block24 : allBlock pairRow 3 192 = true := by decide +kernel
private theorem block25 : allBlock pairRow 3 200 = true := by decide +kernel
private theorem block26 : allBlock pairRow 3 208 = true := by decide +kernel
private theorem block27 : allBlock pairRow 3 216 = true := by decide +kernel
private theorem block28 : allBlock pairRow 3 224 = true := by decide +kernel
private theorem block29 : allBlock pairRow 3 232 = true := by decide +kernel
private theorem block30 : allBlock pairRow 3 240 = true := by decide +kernel
private theorem block31 : allBlock pairRow 3 248 = true := by decide +kernel
private theorem block32 : allBlock pairRow 3 256 = true := by decide +kernel
private theorem block33 : allBlock pairRow 3 264 = true := by decide +kernel
private theorem block34 : allBlock pairRow 3 272 = true := by decide +kernel
private theorem block35 : allBlock pairRow 3 280 = true := by decide +kernel
private theorem block36 : allBlock pairRow 3 288 = true := by decide +kernel
private theorem block37 : allBlock pairRow 3 296 = true := by decide +kernel
private theorem block38 : allBlock pairRow 3 304 = true := by decide +kernel
private theorem block39 : allBlock pairRow 3 312 = true := by decide +kernel
private theorem block40 : allBlock pairRow 3 320 = true := by decide +kernel
private theorem block41 : allBlock pairRow 3 328 = true := by decide +kernel

private theorem block_checked (b : Fin 42) : allBlock pairRow 3 (8*b.val) = true := by
  fin_cases b
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41

/-- Every pair of distinct candidates has explicit labels which do not commute. -/
theorem separation (i j : Fin 330) (hij : i < j) :
    fastMultiply (label i (separator i j).1).val (label j (separator i j).2).val % 8192 ≠
      fastMultiply (label j (separator i j).2).val (label i (separator i j).1).val % 8192 := by
  let b : Fin 42 := ⟨i.val / 8, by omega⟩
  have hr := allBlock_spec pairRow 3 (8*b.val) (block_checked b) i.val
    (by dsimp [b]; omega) (by dsimp [b]; omega)
  have hc := allBlock_spec (pairCheck i.val) 9 0 hr j.val (by omega) (by omega)
  simpa only [pairCheck,dif_pos (show i.val < j.val ∧ j.val < 330 from ⟨hij,j.isLt⟩),
    Bool.not_eq_true',beq_eq_false_iff_ne] using hc

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.OccurrenceTable
