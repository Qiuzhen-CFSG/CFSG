module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.NativeEmbedding

/-!
# Reverse words for the native Suzuki triple

The signed words in `AtlasModel/source/matrix_words.json` express root(1,0),
torus(v), and Weyl in the displayed pair. Each equation is checked by the
kernel using a single matrix multiplication and an explicit intermediate
matrix. Inverse letters use the stored GL inverse before coercion to matrices.

Source context: Aschbacher–Smith I.1.1 and I.1.3(5), printed p.407.
Numerical attribution is in `AtlasModel/source/README.md`. Regenerate with
`Generation/source/generate_reverse_words.py` from the repository root.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.Generation

private def rootOneStep1 : Mat := !![code 6, code 2, code 3, code 2;
     code 4, code 6, code 3, code 5;
     code 4, code 3, code 4, code 7;
     code 7, code 5, code 0, code 2]

private theorem rootOneStep1_eq :
    ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) = rootOneStep1 := by decide +kernel

private def rootOneStep2 : Mat := !![code 7, code 6, code 7, code 4;
     code 1, code 4, code 0, code 7;
     code 5, code 1, code 4, code 6;
     code 6, code 5, code 1, code 7]

private theorem rootOneStep2_eq :
    rootOneStep1 * ((matrixB⁻¹ : GL8) : Mat) = rootOneStep2 := by decide +kernel

private def rootOneStep3 : Mat := !![code 1, code 2, code 3, code 3;
     code 4, code 6, code 1, code 3;
     code 0, code 6, code 7, code 0;
     code 5, code 7, code 1, code 3]

private theorem rootOneStep3_eq :
    rootOneStep2 * ((matrixA : GL8) : Mat) = rootOneStep3 := by decide +kernel

private def rootOneStep4 : Mat := !![code 5, code 7, code 5, code 6;
     code 0, code 6, code 7, code 7;
     code 3, code 5, code 0, code 7;
     code 4, code 3, code 7, code 4]

private theorem rootOneStep4_eq :
    rootOneStep3 * ((matrixB : GL8) : Mat) = rootOneStep4 := by decide +kernel

private def rootOneStep5 : Mat := !![code 3, code 3, code 0, code 3;
     code 1, code 3, code 7, code 3;
     code 5, code 1, code 7, code 4;
     code 1, code 0, code 3, code 2]

private theorem rootOneStep5_eq :
    rootOneStep4 * ((matrixA : GL8) : Mat) = rootOneStep5 := by decide +kernel

private def rootOneStep6 : Mat := !![code 1, code 5, code 6, code 2;
     code 1, code 6, code 4, code 0;
     code 4, code 0, code 6, code 2;
     code 7, code 1, code 3, code 2]

private theorem rootOneStep6_eq :
    rootOneStep5 * ((matrixB : GL8) : Mat) = rootOneStep6 := by decide +kernel

private def rootOneStep7 : Mat := !![code 1, code 7, code 2, code 7;
     code 7, code 5, code 2, code 1;
     code 1, code 5, code 5, code 1;
     code 5, code 5, code 5, code 5]

private theorem rootOneStep7_eq :
    rootOneStep6 * ((matrixB : GL8) : Mat) = rootOneStep7 := by decide +kernel

private def rootOneStep8 : Mat := !![code 7, code 0, code 4, code 2;
     code 0, code 5, code 0, code 2;
     code 1, code 0, code 7, code 3;
     code 4, code 6, code 1, code 1]

private theorem rootOneStep8_eq :
    rootOneStep7 * ((matrixA : GL8) : Mat) = rootOneStep8 := by decide +kernel

private def rootOneStep9 : Mat := !![code 2, code 5, code 7, code 2;
     code 4, code 5, code 0, code 6;
     code 7, code 2, code 3, code 6;
     code 5, code 5, code 2, code 1]

private theorem rootOneStep9_eq :
    rootOneStep8 * ((matrixB⁻¹ : GL8) : Mat) = rootOneStep9 := by decide +kernel

private def rootOneStep10 : Mat := !![code 6, code 3, code 5, code 2;
     code 4, code 4, code 6, code 7;
     code 3, code 3, code 4, code 3;
     code 1, code 5, code 4, code 7]

private theorem rootOneStep10_eq :
    rootOneStep9 * ((matrixA : GL8) : Mat) = rootOneStep10 := by decide +kernel

private def rootOneStep11 : Mat := !![code 1, code 5, code 3, code 3;
     code 1, code 6, code 0, code 7;
     code 5, code 4, code 0, code 2;
     code 4, code 5, code 6, code 6]

private theorem rootOneStep11_eq :
    rootOneStep10 * ((matrixB : GL8) : Mat) = rootOneStep11 := by decide +kernel

private def rootOneStep12 : Mat := !![code 3, code 2, code 1, code 3;
     code 1, code 0, code 4, code 7;
     code 5, code 3, code 3, code 7;
     code 1, code 3, code 1, code 2]

private theorem rootOneStep12_eq :
    rootOneStep11 * ((matrixB : GL8) : Mat) = rootOneStep12 := by decide +kernel

private def rootOneStep13 : Mat := !![code 4, code 7, code 5, code 1;
     code 2, code 2, code 7, code 6;
     code 0, code 2, code 2, code 2;
     code 6, code 6, code 0, code 6]

private theorem rootOneStep13_eq :
    rootOneStep12 * ((matrixA : GL8) : Mat) = rootOneStep13 := by decide +kernel

private def rootOneStep14 : Mat := !![code 4, code 0, code 3, code 7;
     code 3, code 3, code 2, code 7;
     code 7, code 6, code 0, code 2;
     code 4, code 1, code 2, code 5]

private theorem rootOneStep14_eq :
    rootOneStep13 * ((matrixB : GL8) : Mat) = rootOneStep14 := by decide +kernel

private def rootOneStep15 : Mat := !![code 2, code 4, code 3, code 3;
     code 1, code 6, code 3, code 1;
     code 1, code 1, code 7, code 2;
     code 6, code 2, code 0, code 3]

private theorem rootOneStep15_eq :
    rootOneStep14 * ((matrixA : GL8) : Mat) = rootOneStep15 := by decide +kernel

private def rootOneStep16 : Mat := !![code 3, code 5, code 3, code 4;
     code 4, code 2, code 2, code 6;
     code 0, code 4, code 3, code 7;
     code 2, code 7, code 1, code 2]

private theorem rootOneStep16_eq :
    rootOneStep15 * ((matrixB⁻¹ : GL8) : Mat) = rootOneStep16 := by decide +kernel

private def rootOneStep17 : Mat := !![code 1, code 1, code 0, code 1;
     code 0, code 1, code 1, code 1;
     code 1, code 1, code 1, code 0;
     code 1, code 0, code 1, code 1]

private theorem rootOneStep17_eq :
    rootOneStep16 * ((matrixA : GL8) : Mat) = rootOneStep17 := by decide +kernel

private def rootOneStep18 : Mat := !![code 2, code 0, code 3, code 6;
     code 6, code 4, code 7, code 2;
     code 2, code 6, code 2, code 2;
     code 4, code 6, code 3, code 1]

private theorem rootOneStep18_eq :
    rootOneStep17 * ((matrixB⁻¹ : GL8) : Mat) = rootOneStep18 := by decide +kernel

private def rootOneStep19 : Mat := !![code 7, code 1, code 0, code 6;
     code 2, code 2, code 2, code 7;
     code 6, code 2, code 6, code 4;
     code 4, code 3, code 0, code 5]

private theorem rootOneStep19_eq :
    rootOneStep18 * ((matrixA : GL8) : Mat) = rootOneStep19 := by decide +kernel

private def rootOneStep20 : Mat := !![code 4, code 2, code 5, code 2;
     code 2, code 1, code 5, code 4;
     code 0, code 2, code 5, code 0;
     code 6, code 5, code 1, code 7]

private theorem rootOneStep20_eq :
    rootOneStep19 * ((matrixB : GL8) : Mat) = rootOneStep20 := by decide +kernel

private def rootOneStep21 : Mat := !![code 4, code 2, code 5, code 2;
     code 2, code 1, code 5, code 4;
     code 4, code 0, code 0, code 2;
     code 5, code 7, code 1, code 3]

private theorem rootOneStep21_eq :
    rootOneStep20 * ((matrixA : GL8) : Mat) = rootOneStep21 := by decide +kernel

private def rootOneStep22 : Mat := !![code 7, code 1, code 0, code 6;
     code 2, code 2, code 2, code 7;
     code 2, code 4, code 6, code 3;
     code 3, code 6, code 2, code 3]

private theorem rootOneStep22_eq :
    rootOneStep21 * ((matrixB⁻¹ : GL8) : Mat) = rootOneStep22 := by decide +kernel

private def rootOneStep23 : Mat := !![code 2, code 0, code 3, code 6;
     code 6, code 4, code 7, code 2;
     code 0, code 6, code 5, code 7;
     code 5, code 3, code 7, code 3]

private theorem rootOneStep23_eq :
    rootOneStep22 * ((matrixA : GL8) : Mat) = rootOneStep23 := by decide +kernel

private def rootOneStep24 : Mat := !![code 1, code 1, code 0, code 1;
     code 0, code 1, code 1, code 1;
     code 0, code 0, code 1, code 1;
     code 0, code 0, code 0, code 1]

private theorem rootOneStep24_eq :
    rootOneStep23 * ((matrixB : GL8) : Mat) = rootOneStep24 := by decide +kernel

theorem rootOne_word :
    matrixB * matrixA * (matrixB⁻¹) * matrixA * matrixB * matrixA * matrixB * matrixB * matrixA * (matrixB⁻¹)
      * matrixA * matrixB * matrixB * matrixA * matrixB * matrixA * (matrixB⁻¹) * matrixA * (matrixB⁻¹) *
      matrixA * matrixB * matrixA * (matrixB⁻¹) * matrixA * matrixB = rootOne := by
  apply Units.ext
  change ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) :
    Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixB : GL8) :
    Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) :
    Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) :
    Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8)
    : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8)
    : Mat) * ((matrixB : GL8) : Mat) = (rootOne : Mat)
  rw [rootOneStep1_eq, rootOneStep2_eq, rootOneStep3_eq, rootOneStep4_eq, rootOneStep5_eq, rootOneStep6_eq,
    rootOneStep7_eq, rootOneStep8_eq, rootOneStep9_eq, rootOneStep10_eq, rootOneStep11_eq, rootOneStep12_eq,
    rootOneStep13_eq, rootOneStep14_eq, rootOneStep15_eq, rootOneStep16_eq, rootOneStep17_eq,
    rootOneStep18_eq, rootOneStep19_eq, rootOneStep20_eq, rootOneStep21_eq, rootOneStep22_eq,
    rootOneStep23_eq, rootOneStep24_eq]
  rfl

theorem rootOne_mem_pair : rootOne ∈ pairSubgroup := by
  rw [← rootOne_word]
  have ha : matrixA ∈ pairSubgroup := pairA.property
  have hb : matrixB ∈ pairSubgroup := pairB.property
  exact (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem hb ha)
    (pairSubgroup.inv_mem hb)) ha) hb) ha) hb) hb) ha) (pairSubgroup.inv_mem hb)) ha) hb) hb) ha) hb) ha)
    (pairSubgroup.inv_mem hb)) ha) (pairSubgroup.inv_mem hb)) ha) hb) ha) (pairSubgroup.inv_mem hb)) ha) hb)

private def torusVStep1 : Mat := !![code 3, code 0, code 1, code 2;
     code 2, code 7, code 7, code 6;
     code 6, code 3, code 1, code 6;
     code 3, code 5, code 0, code 1]

private theorem torusVStep1_eq :
    ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) = torusVStep1 := by decide +kernel

private def torusVStep2 : Mat := !![code 7, code 5, code 5, code 1;
     code 2, code 4, code 5, code 2;
     code 2, code 2, code 0, code 1;
     code 3, code 7, code 3, code 5]

private theorem torusVStep2_eq :
    torusVStep1 * ((matrixA : GL8) : Mat) = torusVStep2 := by decide +kernel

private def torusVStep3 : Mat := !![code 3, code 0, code 3, code 3;
     code 1, code 7, code 1, code 3;
     code 7, code 6, code 6, code 2;
     code 5, code 0, code 4, code 1]

private theorem torusVStep3_eq :
    torusVStep2 * ((matrixB⁻¹ : GL8) : Mat) = torusVStep3 := by decide +kernel

private def torusVStep4 : Mat := !![code 4, code 2, code 3, code 4;
     code 4, code 5, code 5, code 3;
     code 5, code 0, code 5, code 2;
     code 3, code 5, code 4, code 4]

private theorem torusVStep4_eq :
    torusVStep3 * ((matrixA : GL8) : Mat) = torusVStep4 := by decide +kernel

private def torusVStep5 : Mat := !![code 3, code 4, code 4, code 1;
     code 5, code 2, code 3, code 4;
     code 3, code 2, code 6, code 0;
     code 4, code 6, code 4, code 5]

private theorem torusVStep5_eq :
    torusVStep4 * ((matrixB⁻¹ : GL8) : Mat) = torusVStep5 := by decide +kernel

private def torusVStep6 : Mat := !![code 1, code 3, code 6, code 4;
     code 6, code 0, code 1, code 5;
     code 6, code 3, code 4, code 3;
     code 2, code 2, code 0, code 2]

private theorem torusVStep6_eq :
    torusVStep5 * ((matrixA : GL8) : Mat) = torusVStep6 := by decide +kernel

private def torusVStep7 : Mat := !![code 5, code 7, code 4, code 2;
     code 6, code 5, code 4, code 0;
     code 1, code 0, code 2, code 7;
     code 7, code 4, code 5, code 1]

private theorem torusVStep7_eq :
    torusVStep6 * ((matrixB : GL8) : Mat) = torusVStep7 := by decide +kernel

private def torusVStep8 : Mat := !![code 5, code 4, code 0, code 6;
     code 4, code 4, code 2, code 6;
     code 4, code 5, code 2, code 6;
     code 2, code 5, code 0, code 6]

private theorem torusVStep8_eq :
    torusVStep7 * ((matrixA : GL8) : Mat) = torusVStep8 := by decide +kernel

private def torusVStep9 : Mat := !![code 6, code 5, code 3, code 5;
     code 3, code 0, code 4, code 5;
     code 2, code 2, code 6, code 0;
     code 5, code 3, code 4, code 5]

private theorem torusVStep9_eq :
    torusVStep8 * ((matrixB⁻¹ : GL8) : Mat) = torusVStep9 := by decide +kernel

private def torusVStep10 : Mat := !![code 6, code 3, code 7, code 7;
     code 7, code 1, code 2, code 3;
     code 7, code 3, code 7, code 1;
     code 4, code 0, code 4, code 4]

private theorem torusVStep10_eq :
    torusVStep9 * ((matrixA : GL8) : Mat) = torusVStep10 := by decide +kernel

private def torusVStep11 : Mat := !![code 2, code 6, code 0, code 5;
     code 1, code 7, code 6, code 6;
     code 3, code 0, code 3, code 2;
     code 1, code 6, code 6, code 2]

private theorem torusVStep11_eq :
    torusVStep10 * ((matrixB : GL8) : Mat) = torusVStep11 := by decide +kernel

private def torusVStep12 : Mat := !![code 6, code 2, code 4, code 6;
     code 5, code 4, code 1, code 6;
     code 6, code 3, code 2, code 0;
     code 3, code 5, code 1, code 6]

private theorem torusVStep12_eq :
    torusVStep11 * ((matrixB : GL8) : Mat) = torusVStep12 := by decide +kernel

private def torusVStep13 : Mat := !![code 3, code 7, code 2, code 6;
     code 6, code 1, code 3, code 2;
     code 6, code 2, code 1, code 7;
     code 5, code 6, code 6, code 3]

private theorem torusVStep13_eq :
    torusVStep12 * ((matrixA : GL8) : Mat) = torusVStep13 := by decide +kernel

private def torusVStep14 : Mat := !![code 5, code 2, code 7, code 7;
     code 7, code 3, code 4, code 7;
     code 6, code 1, code 6, code 1;
     code 6, code 4, code 5, code 6]

private theorem torusVStep14_eq :
    torusVStep13 * ((matrixB : GL8) : Mat) = torusVStep14 := by decide +kernel

private def torusVStep15 : Mat := !![code 7, code 2, code 2, code 3;
     code 5, code 4, code 2, code 7;
     code 1, code 6, code 1, code 5;
     code 5, code 0, code 5, code 5]

private theorem torusVStep15_eq :
    torusVStep14 * ((matrixA : GL8) : Mat) = torusVStep15 := by decide +kernel

private def torusVStep16 : Mat := !![code 4, code 4, code 4, code 4;
     code 6, code 4, code 4, code 6;
     code 3, code 6, code 0, code 4;
     code 1, code 3, code 7, code 5]

private theorem torusVStep16_eq :
    torusVStep15 * ((matrixB⁻¹ : GL8) : Mat) = torusVStep16 := by decide +kernel

private def torusVStep17 : Mat := !![code 3, code 5, code 7, code 7;
     code 4, code 2, code 0, code 5;
     code 2, code 0, code 4, code 0;
     code 1, code 7, code 0, code 2]

private theorem torusVStep17_eq :
    torusVStep16 * ((matrixA : GL8) : Mat) = torusVStep17 := by decide +kernel

private def torusVStep18 : Mat := !![code 3, code 2, code 3, code 7;
     code 3, code 6, code 0, code 2;
     code 3, code 6, code 2, code 4;
     code 3, code 2, code 5, code 4]

private theorem torusVStep18_eq :
    torusVStep17 * ((matrixB : GL8) : Mat) = torusVStep18 := by decide +kernel

private def torusVStep19 : Mat := !![code 2, code 5, code 6, code 5;
     code 6, code 1, code 5, code 7;
     code 2, code 1, code 2, code 5;
     code 4, code 2, code 0, code 6]

private theorem torusVStep19_eq :
    torusVStep18 * ((matrixB : GL8) : Mat) = torusVStep19 := by decide +kernel

private def torusVStep20 : Mat := !![code 6, code 4, code 2, code 6;
     code 2, code 6, code 6, code 4;
     code 1, code 2, code 1, code 0;
     code 2, code 2, code 3, code 1]

private theorem torusVStep20_eq :
    torusVStep19 * ((matrixA : GL8) : Mat) = torusVStep20 := by decide +kernel

private def torusVStep21 : Mat := !![code 4, code 0, code 0, code 0;
     code 0, code 3, code 0, code 0;
     code 0, code 0, code 6, code 0;
     code 0, code 0, code 0, code 5]

private theorem torusVStep21_eq :
    torusVStep20 * ((matrixB⁻¹ : GL8) : Mat) = torusVStep21 := by decide +kernel

theorem torusV_word :
    matrixA * matrixB * matrixA * (matrixB⁻¹) * matrixA * (matrixB⁻¹) * matrixA * matrixB * matrixA *
      (matrixB⁻¹) * matrixA * matrixB * matrixB * matrixA * matrixB * matrixA * (matrixB⁻¹) * matrixA *
      matrixB * matrixB * matrixA * (matrixB⁻¹) = torusV := by
  apply Units.ext
  change ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) :
    Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) :
    Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) :
    Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) :
    Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixB : GL8) :
    Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) = (torusV : Mat)
  rw [torusVStep1_eq, torusVStep2_eq, torusVStep3_eq, torusVStep4_eq, torusVStep5_eq, torusVStep6_eq,
    torusVStep7_eq, torusVStep8_eq, torusVStep9_eq, torusVStep10_eq, torusVStep11_eq, torusVStep12_eq,
    torusVStep13_eq, torusVStep14_eq, torusVStep15_eq, torusVStep16_eq, torusVStep17_eq, torusVStep18_eq,
    torusVStep19_eq, torusVStep20_eq, torusVStep21_eq]
  rfl

theorem torusV_mem_pair : torusV ∈ pairSubgroup := by
  rw [← torusV_word]
  have ha : matrixA ∈ pairSubgroup := pairA.property
  have hb : matrixB ∈ pairSubgroup := pairB.property
  exact (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem ha hb) ha) (pairSubgroup.inv_mem hb)) ha) (pairSubgroup.inv_mem hb)) ha) hb) ha)
    (pairSubgroup.inv_mem hb)) ha) hb) hb) ha) hb) ha) (pairSubgroup.inv_mem hb)) ha) hb) hb) ha)
    (pairSubgroup.inv_mem hb))

private def weylStep1 : Mat := !![code 6, code 2, code 3, code 2;
     code 4, code 6, code 3, code 5;
     code 4, code 3, code 4, code 7;
     code 7, code 5, code 0, code 2]

private theorem weylStep1_eq :
    ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) = weylStep1 := by decide +kernel

private def weylStep2 : Mat := !![code 1, code 1, code 5, code 4;
     code 7, code 3, code 2, code 4;
     code 1, code 2, code 3, code 0;
     code 5, code 4, code 2, code 4]

private theorem weylStep2_eq :
    weylStep1 * ((matrixB : GL8) : Mat) = weylStep2 := by decide +kernel

private def weylStep3 : Mat := !![code 4, code 1, code 7, code 3;
     code 3, code 1, code 1, code 6;
     code 6, code 4, code 3, code 5;
     code 5, code 2, code 6, code 6]

private theorem weylStep3_eq :
    weylStep2 * ((matrixA : GL8) : Mat) = weylStep3 := by decide +kernel

private def weylStep4 : Mat := !![code 3, code 5, code 4, code 4;
     code 2, code 5, code 7, code 1;
     code 6, code 7, code 3, code 2;
     code 3, code 0, code 7, code 5]

private theorem weylStep4_eq :
    weylStep3 * ((matrixB⁻¹ : GL8) : Mat) = weylStep4 := by decide +kernel

private def weylStep5 : Mat := !![code 5, code 0, code 4, code 1;
     code 4, code 6, code 3, code 4;
     code 6, code 2, code 2, code 4;
     code 4, code 3, code 5, code 3]

private theorem weylStep5_eq :
    weylStep4 * ((matrixA : GL8) : Mat) = weylStep5 := by decide +kernel

private def weylStep6 : Mat := !![code 3, code 7, code 3, code 5;
     code 5, code 6, code 3, code 6;
     code 2, code 5, code 3, code 0;
     code 7, code 0, code 1, code 4]

private theorem weylStep6_eq :
    weylStep5 * ((matrixB : GL8) : Mat) = weylStep6 := by decide +kernel

private def weylStep7 : Mat := !![code 7, code 7, code 6, code 5;
     code 1, code 6, code 4, code 2;
     code 5, code 3, code 2, code 3;
     code 6, code 6, code 0, code 6]

private theorem weylStep7_eq :
    weylStep6 * ((matrixB : GL8) : Mat) = weylStep7 := by decide +kernel

private def weylStep8 : Mat := !![code 1, code 1, code 4, code 7;
     code 6, code 5, code 4, code 3;
     code 4, code 5, code 1, code 3;
     code 1, code 3, code 1, code 2]

private theorem weylStep8_eq :
    weylStep7 * ((matrixA : GL8) : Mat) = weylStep8 := by decide +kernel

private def weylStep9 : Mat := !![code 7, code 3, code 7, code 2;
     code 0, code 5, code 3, code 1;
     code 7, code 3, code 5, code 6;
     code 7, code 2, code 1, code 1]

private theorem weylStep9_eq :
    weylStep8 * ((matrixB : GL8) : Mat) = weylStep9 := by decide +kernel

private def weylStep10 : Mat := !![code 5, code 1, code 7, code 1;
     code 7, code 4, code 1, code 0;
     code 2, code 4, code 1, code 2;
     code 2, code 0, code 1, code 5]

private theorem weylStep10_eq :
    weylStep9 * ((matrixA : GL8) : Mat) = weylStep10 := by decide +kernel

private def weylStep11 : Mat := !![code 4, code 3, code 7, code 4;
     code 0, code 3, code 6, code 1;
     code 7, code 6, code 4, code 4;
     code 2, code 5, code 3, code 6]

private theorem weylStep11_eq :
    weylStep10 * ((matrixB⁻¹ : GL8) : Mat) = weylStep11 := by decide +kernel

private def weylStep12 : Mat := !![code 1, code 0, code 3, code 2;
     code 4, code 1, code 6, code 2;
     code 6, code 6, code 0, code 3;
     code 1, code 7, code 6, code 1]

private theorem weylStep12_eq :
    weylStep11 * ((matrixA : GL8) : Mat) = weylStep12 := by decide +kernel

private def weylStep13 : Mat := !![code 7, code 1, code 3, code 2;
     code 3, code 7, code 7, code 4;
     code 2, code 0, code 0, code 4;
     code 3, code 1, code 7, code 5]

private theorem weylStep13_eq :
    weylStep12 * ((matrixB : GL8) : Mat) = weylStep13 := by decide +kernel

private def weylStep14 : Mat := !![code 1, code 4, code 4, code 3;
     code 2, code 6, code 1, code 2;
     code 4, code 4, code 0, code 2;
     code 3, code 4, code 3, code 7]

private theorem weylStep14_eq :
    weylStep13 * ((matrixA : GL8) : Mat) = weylStep14 := by decide +kernel

private def weylStep15 : Mat := !![code 7, code 3, code 0, code 4;
     code 3, code 1, code 3, code 2;
     code 0, code 3, code 2, code 5;
     code 4, code 2, code 5, code 2]

private theorem weylStep15_eq :
    weylStep14 * ((matrixB⁻¹ : GL8) : Mat) = weylStep15 := by decide +kernel

private def weylStep16 : Mat := !![code 5, code 2, code 3, code 6;
     code 6, code 4, code 2, code 0;
     code 0, code 3, code 2, code 5;
     code 4, code 2, code 5, code 2]

private theorem weylStep16_eq :
    weylStep15 * ((matrixA : GL8) : Mat) = weylStep16 := by decide +kernel

private def weylStep17 : Mat := !![code 7, code 7, code 0, code 7;
     code 6, code 1, code 5, code 1;
     code 3, code 7, code 2, code 5;
     code 7, code 1, code 0, code 6]

private theorem weylStep17_eq :
    weylStep16 * ((matrixB⁻¹ : GL8) : Mat) = weylStep17 := by decide +kernel

private def weylStep18 : Mat := !![code 2, code 4, code 2, code 3;
     code 0, code 4, code 5, code 5;
     code 2, code 4, code 3, code 1;
     code 2, code 0, code 3, code 6]

private theorem weylStep18_eq :
    weylStep17 * ((matrixA : GL8) : Mat) = weylStep18 := by decide +kernel

private def weylStep19 : Mat := !![code 1, code 3, code 2, code 2;
     code 4, code 5, code 3, code 6;
     code 6, code 5, code 1, code 5;
     code 1, code 1, code 0, code 1]

private theorem weylStep19_eq :
    weylStep18 * ((matrixB : GL8) : Mat) = weylStep19 := by decide +kernel

private def weylStep20 : Mat := !![code 3, code 0, code 2, code 6;
     code 6, code 7, code 5, code 7;
     code 2, code 5, code 4, code 7;
     code 3, code 5, code 3, code 4]

private theorem weylStep20_eq :
    weylStep19 * ((matrixA : GL8) : Mat) = weylStep20 := by decide +kernel

private def weylStep21 : Mat := !![code 1, code 5, code 1, code 3;
     code 0, code 1, code 3, code 3;
     code 3, code 7, code 7, code 0;
     code 2, code 4, code 3, code 3]

private theorem weylStep21_eq :
    weylStep20 * ((matrixB : GL8) : Mat) = weylStep21 := by decide +kernel

private def weylStep22 : Mat := !![code 5, code 5, code 4, code 3;
     code 5, code 1, code 3, code 7;
     code 4, code 3, code 6, code 6;
     code 3, code 7, code 6, code 2]

private theorem weylStep22_eq :
    weylStep21 * ((matrixB : GL8) : Mat) = weylStep22 := by decide +kernel

private def weylStep23 : Mat := !![code 6, code 6, code 2, code 5;
     code 5, code 3, code 4, code 6;
     code 1, code 6, code 0, code 6;
     code 7, code 7, code 4, code 3]

private theorem weylStep23_eq :
    weylStep22 * ((matrixA : GL8) : Mat) = weylStep23 := by decide +kernel

private def weylStep24 : Mat := !![code 3, code 2, code 2, code 7;
     code 7, code 2, code 4, code 5;
     code 3, code 0, code 5, code 5;
     code 5, code 1, code 2, code 1]

private theorem weylStep24_eq :
    weylStep23 * ((matrixB⁻¹ : GL8) : Mat) = weylStep24 := by decide +kernel

private def weylStep25 : Mat := !![code 7, code 4, code 4, code 6;
     code 5, code 3, code 6, code 2;
     code 0, code 4, code 3, code 3;
     code 2, code 7, code 5, code 2]

private theorem weylStep25_eq :
    weylStep24 * ((matrixA : GL8) : Mat) = weylStep25 := by decide +kernel

private def weylStep26 : Mat := !![code 7, code 1, code 6, code 5;
     code 1, code 3, code 6, code 0;
     code 6, code 6, code 2, code 1;
     code 5, code 0, code 1, code 3]

private theorem weylStep26_eq :
    weylStep25 * ((matrixB : GL8) : Mat) = weylStep26 := by decide +kernel

private def weylStep27 : Mat := !![code 0, code 0, code 0, code 1;
     code 0, code 0, code 1, code 0;
     code 0, code 1, code 0, code 0;
     code 1, code 0, code 0, code 0]

private theorem weylStep27_eq :
    weylStep26 * ((matrixA : GL8) : Mat) = weylStep27 := by decide +kernel

theorem weyl_word :
    matrixB * matrixA * matrixB * matrixA * (matrixB⁻¹) * matrixA * matrixB * matrixB * matrixA * matrixB *
      matrixA * (matrixB⁻¹) * matrixA * matrixB * matrixA * (matrixB⁻¹) * matrixA * (matrixB⁻¹) * matrixA *
      matrixB * matrixA * matrixB * matrixB * matrixA * (matrixB⁻¹) * matrixA * matrixB * matrixA = weyl := by
  apply Units.ext
  change ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat)
    * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixB : GL8) : Mat)
    * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat)
    * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat)
    * ((matrixA : GL8) : Mat) * ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat)
    * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) *
    ((matrixB⁻¹ : GL8) : Mat) * ((matrixA : GL8) : Mat) * ((matrixB : GL8) : Mat) * ((matrixA : GL8) : Mat) =
    (weyl : Mat)
  rw [weylStep1_eq, weylStep2_eq, weylStep3_eq, weylStep4_eq, weylStep5_eq, weylStep6_eq, weylStep7_eq,
    weylStep8_eq, weylStep9_eq, weylStep10_eq, weylStep11_eq, weylStep12_eq, weylStep13_eq, weylStep14_eq,
    weylStep15_eq, weylStep16_eq, weylStep17_eq, weylStep18_eq, weylStep19_eq, weylStep20_eq, weylStep21_eq,
    weylStep22_eq, weylStep23_eq, weylStep24_eq, weylStep25_eq, weylStep26_eq, weylStep27_eq]
  rfl

theorem weyl_mem_pair : weyl ∈ pairSubgroup := by
  rw [← weyl_word]
  have ha : matrixA ∈ pairSubgroup := pairA.property
  have hb : matrixB ∈ pairSubgroup := pairB.property
  exact (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem
    (pairSubgroup.mul_mem (pairSubgroup.mul_mem (pairSubgroup.mul_mem hb ha) hb) ha) (pairSubgroup.inv_mem
    hb)) ha) hb) hb) ha) hb) ha) (pairSubgroup.inv_mem hb)) ha) hb) ha) (pairSubgroup.inv_mem hb)) ha)
    (pairSubgroup.inv_mem hb)) ha) hb) ha) hb) hb) ha) (pairSubgroup.inv_mem hb)) ha) hb) ha)

theorem tripleSubgroup_le_pair : tripleSubgroup ≤ pairSubgroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | hg
  · exact rootOne_mem_pair
  · rcases hg with rfl | hg
    · exact torusV_mem_pair
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact weyl_mem_pair

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.Generation
