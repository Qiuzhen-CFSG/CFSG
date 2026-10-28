module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.StandardModule

/-!
# Checked displacement minors for the two marked Rudvalis involutions

The 14 by 14 and 12 by 12 minors below have explicit left inverses. The
square of the second generator is also checked against a cached matrix.
All three equalities are kernel computations, independent of the Python
certificate generator in `../source/GenerateDisplacement.py`.

The matrices retain the inverse-transpose convention of StandardModule.
Source: Wilson--Nickerson--Bray ATLAS, RuG1-f2r28B0, preserved and attributed
in RudvalisExclusion/source/README.md. Application: Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1, manuscript p.17.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.DisplacementCertificate

def rowsA : Fin 14 → Fin 28 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 17]
def colsA : Fin 14 → Fin 28 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def inverseA : Matrix (Fin 14) (Fin 14) (ZMod 2) :=
  fun i j => if (37951740031438644819039694694497123311379047943001235187683 : ℕ).testBit (14 * i.val + j.val) then 1 else 0

theorem minorA_inverse : inverseA * (matrixA - 1).submatrix rowsA colsA = 1 := by decide +kernel
def matrixBSq : Matrix (Fin 28) (Fin 28) (ZMod 2) :=
  fun i j => if (84058331970430333543844020783100026087890505986641022386141270637155675872852844723524645321537721291597025325182635886662174062354059229707026436915318860319484807880978186980056977228338874114830875826723104453992721901679097118027497 : ℕ).testBit (28 * i.val + j.val) then 1 else 0

theorem matrixB_sq : matrixB * matrixB = matrixBSq := by decide +kernel

def rowsBSq : Fin 12 → Fin 28 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12]
def colsBSq : Fin 12 → Fin 28 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 15]
def inverseBSq : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => if (10406974948788265546183096219696905363529460 : ℕ).testBit (12 * i.val + j.val) then 1 else 0

theorem minorBSq_inverse : inverseBSq * (matrixBSq - 1).submatrix rowsBSq colsBSq = 1 := by decide +kernel

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.DisplacementCertificate
