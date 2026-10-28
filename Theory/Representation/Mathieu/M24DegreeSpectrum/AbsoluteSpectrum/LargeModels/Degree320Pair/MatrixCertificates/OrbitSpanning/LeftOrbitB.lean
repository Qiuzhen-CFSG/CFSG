module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.Arithmetic

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.Data

/-!
# Kernel-checked LeftOrbitB certificate

The numerical rows come from the unchanged ATLAS files and the preserved
`../source/density-candidates-complete.json`. Eight-row checks are assembled
in a balanced tree; each finite assertion is reduced by Lean's kernel.
See `source/README.md` for conventions and representative measurements.
-/

set_option Elab.async false

public section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates.LeftOrbitB

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates

open Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels

private def indices0 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

private theorem h0 : indices0.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices1 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]

private theorem h1 : indices1.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices2 : List Nat := [16, 17, 18, 19, 20, 21, 22, 23]

private theorem h2 : indices2.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices3 : List Nat := [24, 25, 26, 27, 28, 29, 30, 31]

private theorem h3 : indices3.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices4 : List Nat := [32, 33, 34, 35, 36, 37, 38, 39]

private theorem h4 : indices4.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices5 : List Nat := [40, 41, 42, 43, 44, 45, 46, 47]

private theorem h5 : indices5.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices6 : List Nat := [48, 49, 50, 51, 52, 53, 54, 55]

private theorem h6 : indices6.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices7 : List Nat := [56, 57, 58, 59, 60, 61, 62, 63]

private theorem h7 : indices7.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices8 : List Nat := [64, 65, 66, 67, 68, 69, 70, 71]

private theorem h8 : indices8.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices9 : List Nat := [72, 73, 74, 75, 76, 77, 78, 79]

private theorem h9 : indices9.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices10 : List Nat := [80, 81, 82, 83, 84, 85, 86, 87]

private theorem h10 : indices10.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices11 : List Nat := [88, 89, 90, 91, 92, 93, 94, 95]

private theorem h11 : indices11.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices12 : List Nat := [96, 97, 98, 99, 100, 101, 102, 103]

private theorem h12 : indices12.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices13 : List Nat := [104, 105, 106, 107, 108, 109, 110, 111]

private theorem h13 : indices13.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices14 : List Nat := [112, 113, 114, 115, 116, 117, 118, 119]

private theorem h14 : indices14.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices15 : List Nat := [120, 121, 122, 123, 124, 125, 126, 127]

private theorem h15 : indices15.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices16 : List Nat := [128, 129, 130, 131, 132, 133, 134, 135]

private theorem h16 : indices16.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices17 : List Nat := [136, 137, 138, 139, 140, 141, 142, 143]

private theorem h17 : indices17.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices18 : List Nat := [144, 145, 146, 147, 148, 149, 150, 151]

private theorem h18 : indices18.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices19 : List Nat := [152, 153, 154, 155, 156, 157, 158, 159]

private theorem h19 : indices19.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices20 : List Nat := [160, 161, 162, 163, 164, 165, 166, 167]

private theorem h20 : indices20.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices21 : List Nat := [168, 169, 170, 171, 172, 173, 174, 175]

private theorem h21 : indices21.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices22 : List Nat := [176, 177, 178, 179, 180, 181, 182, 183]

private theorem h22 : indices22.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices23 : List Nat := [184, 185, 186, 187, 188, 189, 190, 191]

private theorem h23 : indices23.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices24 : List Nat := [192, 193, 194, 195, 196, 197, 198, 199]

private theorem h24 : indices24.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices25 : List Nat := [200, 201, 202, 203, 204, 205, 206, 207]

private theorem h25 : indices25.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices26 : List Nat := [208, 209, 210, 211, 212, 213, 214, 215]

private theorem h26 : indices26.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices27 : List Nat := [216, 217, 218, 219, 220, 221, 222, 223]

private theorem h27 : indices27.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices28 : List Nat := [224, 225, 226, 227, 228, 229, 230, 231]

private theorem h28 : indices28.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices29 : List Nat := [232, 233, 234, 235, 236, 237, 238, 239]

private theorem h29 : indices29.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices30 : List Nat := [240, 241, 242, 243, 244, 245, 246, 247]

private theorem h30 : indices30.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices31 : List Nat := [248, 249, 250, 251, 252, 253, 254, 255]

private theorem h31 : indices31.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices32 : List Nat := [256, 257, 258, 259, 260, 261, 262, 263]

private theorem h32 : indices32.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices33 : List Nat := [264, 265, 266, 267, 268, 269, 270, 271]

private theorem h33 : indices33.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices34 : List Nat := [272, 273, 274, 275, 276, 277, 278, 279]

private theorem h34 : indices34.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices35 : List Nat := [280, 281, 282, 283, 284, 285, 286, 287]

private theorem h35 : indices35.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices36 : List Nat := [288, 289, 290, 291, 292, 293, 294, 295]

private theorem h36 : indices36.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices37 : List Nat := [296, 297, 298, 299, 300, 301, 302, 303]

private theorem h37 : indices37.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices38 : List Nat := [304, 305, 306, 307, 308, 309, 310, 311]

private theorem h38 : indices38.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

private def indices39 : List Nat := [312, 313, 314, 315, 316, 317, 318, 319]

private theorem h39 : indices39.all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by decide +kernel

theorem steps : (List.range 320).all (orbitStep Data.ABTranspose Data.BBTranspose Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords) = true := by
  have hi : List.range 320 = (((((indices0 ++ indices1) ++ (indices2 ++ (indices3 ++ indices4))) ++ ((indices5 ++ indices6) ++ (indices7 ++ (indices8 ++ indices9)))) ++ (((indices10 ++ indices11) ++ (indices12 ++ (indices13 ++ indices14))) ++ ((indices15 ++ indices16) ++ (indices17 ++ (indices18 ++ indices19))))) ++ ((((indices20 ++ indices21) ++ (indices22 ++ (indices23 ++ indices24))) ++ ((indices25 ++ indices26) ++ (indices27 ++ (indices28 ++ indices29)))) ++ (((indices30 ++ indices31) ++ (indices32 ++ (indices33 ++ indices34))) ++ ((indices35 ++ indices36) ++ (indices37 ++ (indices38 ++ indices39)))))) := by decide +kernel
  rw [hi]
  exact (all_append _ _ _ (all_append _ _ _ (all_append _ _ _ (all_append _ _ _ (all_append _ _ _ h0 h1) (all_append _ _ _ h2 (all_append _ _ _ h3 h4))) (all_append _ _ _ (all_append _ _ _ h5 h6) (all_append _ _ _ h7 (all_append _ _ _ h8 h9)))) (all_append _ _ _ (all_append _ _ _ (all_append _ _ _ h10 h11) (all_append _ _ _ h12 (all_append _ _ _ h13 h14))) (all_append _ _ _ (all_append _ _ _ h15 h16) (all_append _ _ _ h17 (all_append _ _ _ h18 h19))))) (all_append _ _ _ (all_append _ _ _ (all_append _ _ _ (all_append _ _ _ h20 h21) (all_append _ _ _ h22 (all_append _ _ _ h23 h24))) (all_append _ _ _ (all_append _ _ _ h25 h26) (all_append _ _ _ h27 (all_append _ _ _ h28 h29)))) (all_append _ _ _ (all_append _ _ _ (all_append _ _ _ h30 h31) (all_append _ _ _ h32 (all_append _ _ _ h33 h34))) (all_append _ _ _ (all_append _ _ _ h35 h36) (all_append _ _ _ h37 (all_append _ _ _ h38 h39))))))

theorem check : OneSixty.checkOrbit 320 Data.ABTranspose Data.BBTranspose WitnessData.columnB Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords = true :=
  orbit_check 320 Data.ABTranspose Data.BBTranspose WitnessData.columnB Data.leftBColumns Data.leftBParents Data.leftBLetters Data.leftBWords
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) steps

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitCertificates.LeftOrbitB
