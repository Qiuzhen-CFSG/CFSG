module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# The published degree-twenty binary HS matrices

Exact row-major transcription of ATLAS HSG1-f2r20B0. Bit j of a packed
row is column j. Matrices are neither inverted nor transposed. The original
files and a reproducible certificate generator are retained in `source/`.
The extra matrices are witnesses only; `Generators` checks their identities.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/HSG1-f2r20B0 .
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.Twenty

abbrev BinaryMatrix := Matrix (Fin 20) (Fin 20) (ZMod 2)

def aRows : Array ℕ := #[2, 1, 16, 64, 4, 256, 8, 2048, 32, 8192, 16384, 128, 21812, 512, 1024, 41495, 67735, 212758, 279840, 605750]

def aMatrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 aRows

def bRows : Array ℕ := #[4, 8, 32, 128, 181, 512, 1024, 530, 4096, 549, 32768, 65536, 131072, 262144, 524288, 336017, 216518, 938386, 191412, 714779]

def bMatrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 bRows

def bInvRows : Array ℕ := #[549, 664, 1, 2, 568, 4, 369873, 8, 802962, 32, 64, 446376, 256, 43029, 930106, 1024, 2048, 4096, 8192, 16384]

def bInvMatrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 bInvRows

def xRows : Array ℕ := #[8, 4, 181, 1024, 32, 4096, 128, 65536, 512, 262144, 524288, 530, 692885, 549, 32768, 74285, 151373, 691948, 686516, 927077]

def xMatrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 xRows

def x2Rows : Array ℕ := #[1024, 181, 69789, 524288, 4096, 692885, 65536, 151373, 262144, 686516, 927077, 262180, 662444, 266429, 74285, 416213, 395971, 565123, 1027006, 442917]

def x2Matrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 x2Rows

def x4Rows : Array ℕ := #[927077, 645445, 481983, 442917, 662444, 732603, 395971, 390598, 1027006, 567803, 345544, 272822, 1045215, 289111, 779714, 935496, 656981, 825169, 922067, 110713]

def x4Matrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 x4Rows

def x8Rows : Array ℕ := #[649592, 331880, 176364, 908946, 966371, 553534, 656874, 900365, 833100, 256633, 8466, 768679, 8516, 436414, 402326, 391148, 370094, 943802, 882451, 1]

def x8Matrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 x8Rows

def x10Rows : Array ℕ := #[8466, 10308, 2, 1, 8516, 16, 370094, 64, 882451, 256, 8, 505281, 32, 41089, 922193, 16384, 128, 21812, 512, 1024]

def x10Matrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 x10Rows

def differenceRows : Array ℕ := #[9, 6, 177, 1032, 48, 4128, 192, 65664, 768, 262656, 525312, 2578, 688789, 8741, 49152, 107053, 216909, 560876, 948660, 402789]

def differenceMatrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 differenceRows

def differenceInvRows : Array ℕ := #[175302, 89557, 89559, 175303, 747204, 747220, 175250, 175314, 293426, 293682, 175311, 935971, 747252, 838903, 57493, 41109, 175186, 809071, 293170, 174287]

def differenceInvMatrix : BinaryMatrix := Thompson.BinaryMatrix.decode 20 differenceInvRows

end Sporadic.LeechRelated.HS.Twenty
