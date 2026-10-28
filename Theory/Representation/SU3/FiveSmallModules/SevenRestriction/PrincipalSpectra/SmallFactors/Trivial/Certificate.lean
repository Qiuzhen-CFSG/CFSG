module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Data
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Trivial.Normal

/-!
# Six checked similarities for the binary degree-20 quotient

Packed binary matrix products compute the word A₀³A₁A₀A₁ and its six
nonidentity powers. For each power, explicit mutually inverse basis matrices
intertwine it with the same block model: three copies of each nontrivial
cubic companion block and two fixed lines. All finite arithmetic is checked
by kernel reduction through the proved packed binary matrix checker.
The characteristic-polynomial proof then uses only small algebraic identities.

The witnesses and their generator are retained in `Trivial/source/`.
The connection to the actual quotient and coefficient-field transport is in
`Quotient.lean`; these binary identities alone do not assert that connection.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Matrix Polynomial Thompson.BinaryMatrix
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
open Degrees.TrivialCalculation.MiddleFactors
def prefixRows : Fin 6 → Array ℕ := ![
  #[517886, 426114, 98039, 390143, 352255, 456703, 524420, 124031, 1048191, 956672, 1047807, 2048, 924576, 97663, 1013487, 618111, 311424, 753023, 430528, 96127],
  #[486750, 255549, 1042751, 389119, 133120, 372479, 126455, 137824, 920320, 268384, 95871, 2048, 326815, 694720, 251647, 299616, 93487, 37824, 820196, 264384],
  #[557022, 622105, 428964, 262304, 750975, 297008, 654239, 327844, 914623, 423195, 784063, 2048, 84868, 748891, 621759, 100964, 646427, 1046107, 98892, 1015099],
  #[818077, 51658, 168997, 393284, 708539, 403136, 389119, 439845, 510879, 19418, 487327, 17408, 307301, 850866, 445407, 759393, 380890, 646074, 563809, 217050],
  #[84358, 227689, 236457, 299724, 284908, 266436, 262304, 716310, 985892, 119273, 582875, 35344, 587282, 736114, 248608, 117541, 332329, 910514, 98853, 102633],
  #[83573, 920170, 428110, 547917, 698925, 802925, 393284, 111601, 430113, 970286, 575894, 13984, 78744, 943096, 444256, 496163, 522314, 431572, 230403, 695310]]

def powerRows : Fin 6 → Array ℕ := ![
  #[83573, 920170, 428110, 547917, 698925, 802925, 393284, 111601, 430113, 970286, 575894, 13984, 78744, 943096, 444256, 496163, 522314, 431572, 230403, 695310],
  #[7341, 877401, 289657, 787954, 578196, 658738, 367069, 490374, 964212, 292742, 980020, 304196, 242612, 422646, 955172, 625274, 822397, 423949, 96820, 166206],
  #[765252, 764545, 702472, 528933, 632169, 689895, 454813, 665575, 469608, 243023, 598882, 144452, 8237, 758568, 768590, 176842, 593258, 205313, 62922, 103775],
  #[845654, 789825, 827764, 978926, 628281, 1027016, 1023838, 51762, 28303, 28210, 988144, 99368, 897507, 70148, 726384, 97323, 990557, 34365, 112902, 143923],
  #[168290, 12587, 7101, 735210, 143935, 394015, 131345, 478695, 966253, 423338, 16881, 835551, 265698, 953778, 291259, 901187, 266499, 585133, 73388, 961989],
  #[192013, 168062, 102640, 627606, 31174, 425449, 780717, 554595, 306397, 621275, 18625, 916211, 529062, 992054, 838337, 457055, 748453, 631880, 253269, 552603]]

def basisRows : Fin 6 → Array ℕ := ![
  #[839341, 862678, 648304, 247051, 240268, 319068, 491428, 332128, 651302, 948607, 24466, 975107, 443892, 285860, 27654, 870676, 347156, 150676, 745650, 533936],
  #[978719, 937186, 567376, 256429, 247598, 458318, 343734, 397808, 569394, 998907, 32420, 893317, 387286, 292150, 9218, 945574, 418854, 222502, 598292, 542864],
  #[930909, 869300, 753410, 137515, 71011, 376423, 306278, 509446, 585782, 845705, 101460, 1005608, 414498, 361638, 196784, 936356, 409764, 156836, 730130, 593154],
  #[896907, 1009012, 707680, 240799, 254874, 376426, 417554, 463056, 708628, 873725, 16182, 835719, 306530, 276882, 18436, 992434, 469042, 76210, 672166, 552224],
  #[883819, 993058, 679558, 70799, 203991, 458325, 387156, 502276, 643108, 903961, 166002, 930824, 341654, 429460, 131488, 861458, 336274, 85394, 683062, 723078],
  #[1005647, 944790, 606084, 204189, 137717, 319091, 443506, 516610, 700434, 959145, 33894, 883736, 490420, 297266, 65808, 1010870, 483638, 207158, 608292, 656772]]

def inverseRows : Fin 6 → Array ℕ := ![
  #[1037931, 639179, 214155, 783192, 554627, 613528, 509747, 459406, 691480, 137701, 949274, 867630, 739566, 1026197, 404961, 533819, 802939, 744531, 204454, 356610],
  #[1037931, 689216, 639179, 230875, 76315, 554627, 509747, 888726, 459406, 812543, 213300, 949274, 739566, 623988, 1026197, 288064, 465960, 802939, 204454, 356610],
  #[710979, 76315, 554627, 348715, 639179, 214155, 88273, 213300, 949274, 673957, 459406, 691480, 997651, 465960, 802939, 183706, 1026197, 404961, 204454, 356610],
  #[1037931, 214155, 689216, 176064, 613528, 76315, 509747, 691480, 888726, 992459, 867630, 213300, 739566, 404961, 623988, 227688, 744531, 465960, 204454, 356610],
  #[710979, 554627, 613528, 399008, 214155, 689216, 88273, 949274, 867630, 50621, 691480, 888726, 997651, 802939, 744531, 319611, 404961, 623988, 204454, 356610],
  #[710979, 613528, 76315, 824032, 689216, 639179, 88273, 867630, 213300, 870955, 888726, 459406, 997651, 744531, 465960, 877839, 623988, 1026197, 204454, 356610]]

def productRows : Fin 6 → Array ℕ := ![
  #[927574, 842959, 717624, 107169, 120162, 419626, 505842, 311728, 700471, 998811, 26573, 880769, 336634, 290674, 32263, 830602, 306698, 208714, 782717, 545784],
  #[882347, 994933, 679176, 130518, 109207, 341799, 300927, 475384, 659517, 1023705, 14194, 971206, 457807, 275135, 20997, 1015799, 487991, 258743, 577674, 535880],
  #[987950, 829946, 767621, 216209, 50097, 431923, 417591, 371207, 667711, 949220, 167690, 1043472, 485557, 426871, 229752, 994802, 467314, 226162, 774669, 560773],
  #[972769, 1045434, 601904, 122731, 129517, 431893, 485005, 507976, 614410, 844382, 5823, 926019, 417717, 269773, 11266, 1037181, 515133, 56829, 729591, 556720],
  #[835345, 1039029, 747335, 50019, 249419, 341774, 457994, 381954, 712754, 959660, 68925, 987680, 301903, 331722, 197104, 840333, 315853, 45005, 753215, 757063],
  #[1043747, 1013071, 563138, 249838, 216318, 419641, 336701, 391173, 593933, 874836, 131895, 835112, 505338, 396477, 32904, 1048447, 520383, 253119, 568370, 721858]]

def normalRows : Array ℕ := #[4, 5, 2, 32, 8, 48, 256, 320, 128, 2048, 512, 3072, 16384, 20480, 8192, 131072, 32768, 196608, 262144, 524288]

theorem decode_normal : decode 20 normalRows = normal := by decide +kernel

def binaryWord : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  factor20 0 ^ 3 * factor20 1 * factor20 0 * factor20 1

private theorem prefix_1 : factor20 0 * factor20 0 = decode 20 (prefixRows 1) :=
  decode_mul 20 (factorRows20 0) (factorRows20 0) (prefixRows 1) (by decide +kernel)

private theorem prefix_2 : decode 20 (prefixRows 1) * factor20 0 = decode 20 (prefixRows 2) :=
  decode_mul 20 (prefixRows 1) (factorRows20 0) (prefixRows 2) (by decide +kernel)

private theorem prefix_3 : decode 20 (prefixRows 2) * factor20 1 = decode 20 (prefixRows 3) :=
  decode_mul 20 (prefixRows 2) (factorRows20 1) (prefixRows 3) (by decide +kernel)

private theorem prefix_4 : decode 20 (prefixRows 3) * factor20 0 = decode 20 (prefixRows 4) :=
  decode_mul 20 (prefixRows 3) (factorRows20 0) (prefixRows 4) (by decide +kernel)

private theorem prefix_5 : decode 20 (prefixRows 4) * factor20 1 = decode 20 (prefixRows 5) :=
  decode_mul 20 (prefixRows 4) (factorRows20 1) (prefixRows 5) (by decide +kernel)

theorem word_rows : binaryWord = decode 20 (powerRows 0) := by
  simp only [binaryWord, pow_succ, pow_zero, one_mul]
  rw [prefix_1, prefix_2, prefix_3, prefix_4, prefix_5]
  rfl

private theorem power_1 : decode 20 (powerRows 0) * decode 20 (powerRows 0) =
    decode 20 (powerRows 1) :=
  decode_mul 20 (powerRows 0) (powerRows 0) (powerRows 1) (by decide +kernel)

private theorem power_2 : decode 20 (powerRows 1) * decode 20 (powerRows 0) =
    decode 20 (powerRows 2) :=
  decode_mul 20 (powerRows 1) (powerRows 0) (powerRows 2) (by decide +kernel)

private theorem power_3 : decode 20 (powerRows 2) * decode 20 (powerRows 0) =
    decode 20 (powerRows 3) :=
  decode_mul 20 (powerRows 2) (powerRows 0) (powerRows 3) (by decide +kernel)

private theorem power_4 : decode 20 (powerRows 3) * decode 20 (powerRows 0) =
    decode 20 (powerRows 4) :=
  decode_mul 20 (powerRows 3) (powerRows 0) (powerRows 4) (by decide +kernel)

private theorem power_5 : decode 20 (powerRows 4) * decode 20 (powerRows 0) =
    decode 20 (powerRows 5) :=
  decode_mul 20 (powerRows 4) (powerRows 0) (powerRows 5) (by decide +kernel)

theorem powers_rows (k : Fin 6) : binaryWord ^ (k.val + 1) = decode 20 (powerRows k) := by
  fin_cases k
  · change binaryWord ^ 1 = decode 20 (powerRows 0)
    simpa only [pow_one] using word_rows
  · change binaryWord ^ 2 = decode 20 (powerRows 1)
    simp only [pow_succ, pow_zero, one_mul, word_rows]
    rw [power_1]
  · change binaryWord ^ 3 = decode 20 (powerRows 2)
    simp only [pow_succ, pow_zero, one_mul, word_rows]
    rw [power_1, power_2]
  · change binaryWord ^ 4 = decode 20 (powerRows 3)
    simp only [pow_succ, pow_zero, one_mul, word_rows]
    rw [power_1, power_2, power_3]
  · change binaryWord ^ 5 = decode 20 (powerRows 4)
    simp only [pow_succ, pow_zero, one_mul, word_rows]
    rw [power_1, power_2, power_3, power_4]
  · change binaryWord ^ 6 = decode 20 (powerRows 5)
    simp only [pow_succ, pow_zero, one_mul, word_rows]
    rw [power_1, power_2, power_3, power_4, power_5]

private theorem basis_inverse_0 : decode 20 (basisRows 0) * decode 20 (inverseRows 0) = 1 :=
  decode_mul_one 20 (basisRows 0) (inverseRows 0) (by decide +kernel)
private theorem action_basis_0 : decode 20 (powerRows 0) * decode 20 (basisRows 0) =
    decode 20 (productRows 0) :=
  decode_mul 20 (powerRows 0) (basisRows 0) (productRows 0) (by decide +kernel)
private theorem basis_normal_0 : decode 20 (basisRows 0) * decode 20 normalRows =
    decode 20 (productRows 0) :=
  decode_mul 20 (basisRows 0) normalRows (productRows 0) (by decide +kernel)

private theorem basis_inverse_1 : decode 20 (basisRows 1) * decode 20 (inverseRows 1) = 1 :=
  decode_mul_one 20 (basisRows 1) (inverseRows 1) (by decide +kernel)
private theorem action_basis_1 : decode 20 (powerRows 1) * decode 20 (basisRows 1) =
    decode 20 (productRows 1) :=
  decode_mul 20 (powerRows 1) (basisRows 1) (productRows 1) (by decide +kernel)
private theorem basis_normal_1 : decode 20 (basisRows 1) * decode 20 normalRows =
    decode 20 (productRows 1) :=
  decode_mul 20 (basisRows 1) normalRows (productRows 1) (by decide +kernel)

private theorem basis_inverse_2 : decode 20 (basisRows 2) * decode 20 (inverseRows 2) = 1 :=
  decode_mul_one 20 (basisRows 2) (inverseRows 2) (by decide +kernel)
private theorem action_basis_2 : decode 20 (powerRows 2) * decode 20 (basisRows 2) =
    decode 20 (productRows 2) :=
  decode_mul 20 (powerRows 2) (basisRows 2) (productRows 2) (by decide +kernel)
private theorem basis_normal_2 : decode 20 (basisRows 2) * decode 20 normalRows =
    decode 20 (productRows 2) :=
  decode_mul 20 (basisRows 2) normalRows (productRows 2) (by decide +kernel)

private theorem basis_inverse_3 : decode 20 (basisRows 3) * decode 20 (inverseRows 3) = 1 :=
  decode_mul_one 20 (basisRows 3) (inverseRows 3) (by decide +kernel)
private theorem action_basis_3 : decode 20 (powerRows 3) * decode 20 (basisRows 3) =
    decode 20 (productRows 3) :=
  decode_mul 20 (powerRows 3) (basisRows 3) (productRows 3) (by decide +kernel)
private theorem basis_normal_3 : decode 20 (basisRows 3) * decode 20 normalRows =
    decode 20 (productRows 3) :=
  decode_mul 20 (basisRows 3) normalRows (productRows 3) (by decide +kernel)

private theorem basis_inverse_4 : decode 20 (basisRows 4) * decode 20 (inverseRows 4) = 1 :=
  decode_mul_one 20 (basisRows 4) (inverseRows 4) (by decide +kernel)
private theorem action_basis_4 : decode 20 (powerRows 4) * decode 20 (basisRows 4) =
    decode 20 (productRows 4) :=
  decode_mul 20 (powerRows 4) (basisRows 4) (productRows 4) (by decide +kernel)
private theorem basis_normal_4 : decode 20 (basisRows 4) * decode 20 normalRows =
    decode 20 (productRows 4) :=
  decode_mul 20 (basisRows 4) normalRows (productRows 4) (by decide +kernel)

private theorem basis_inverse_5 : decode 20 (basisRows 5) * decode 20 (inverseRows 5) = 1 :=
  decode_mul_one 20 (basisRows 5) (inverseRows 5) (by decide +kernel)
private theorem action_basis_5 : decode 20 (powerRows 5) * decode 20 (basisRows 5) =
    decode 20 (productRows 5) :=
  decode_mul 20 (powerRows 5) (basisRows 5) (productRows 5) (by decide +kernel)
private theorem basis_normal_5 : decode 20 (basisRows 5) * decode 20 normalRows =
    decode 20 (productRows 5) :=
  decode_mul 20 (basisRows 5) normalRows (productRows 5) (by decide +kernel)

theorem normal_certificate (k : Fin 6) :
    decode 20 (basisRows k) * decode 20 (inverseRows k) = 1 ∧
    decode 20 (powerRows k) * decode 20 (basisRows k) = decode 20 (basisRows k) * normal := by
  rw [← decode_normal]
  fin_cases k
  · exact ⟨basis_inverse_0, action_basis_0.trans basis_normal_0.symm⟩
  · exact ⟨basis_inverse_1, action_basis_1.trans basis_normal_1.symm⟩
  · exact ⟨basis_inverse_2, action_basis_2.trans basis_normal_2.symm⟩
  · exact ⟨basis_inverse_3, action_basis_3.trans basis_normal_3.symm⟩
  · exact ⟨basis_inverse_4, action_basis_4.trans basis_normal_4.symm⟩
  · exact ⟨basis_inverse_5, action_basis_5.trans basis_normal_5.symm⟩

private theorem inverse_basis_0 : decode 20 (inverseRows 0) * decode 20 (basisRows 0) = 1 :=
  decode_mul_one 20 (inverseRows 0) (basisRows 0) (by decide +kernel)
private theorem inverse_basis_1 : decode 20 (inverseRows 1) * decode 20 (basisRows 1) = 1 :=
  decode_mul_one 20 (inverseRows 1) (basisRows 1) (by decide +kernel)
private theorem inverse_basis_2 : decode 20 (inverseRows 2) * decode 20 (basisRows 2) = 1 :=
  decode_mul_one 20 (inverseRows 2) (basisRows 2) (by decide +kernel)
private theorem inverse_basis_3 : decode 20 (inverseRows 3) * decode 20 (basisRows 3) = 1 :=
  decode_mul_one 20 (inverseRows 3) (basisRows 3) (by decide +kernel)
private theorem inverse_basis_4 : decode 20 (inverseRows 4) * decode 20 (basisRows 4) = 1 :=
  decode_mul_one 20 (inverseRows 4) (basisRows 4) (by decide +kernel)
private theorem inverse_basis_5 : decode 20 (inverseRows 5) * decode 20 (basisRows 5) = 1 :=
  decode_mul_one 20 (inverseRows 5) (basisRows 5) (by decide +kernel)

private theorem inverse_basis (k : Fin 6) : decode 20 (inverseRows k) * decode 20 (basisRows k) = 1 := by
  fin_cases k
  · exact inverse_basis_0
  · exact inverse_basis_1
  · exact inverse_basis_2
  · exact inverse_basis_3
  · exact inverse_basis_4
  · exact inverse_basis_5

private theorem charpoly_of_certificate (A B C D : Matrix (Fin 20) (Fin 20) (ZMod 2))
    (hBC : B * C = 1) (hCB : C * B = 1) (hAB : A * B = B * D) : A.charpoly = D.charpoly := by
  calc
    A.charpoly = (A * B * C).charpoly := by rw [Matrix.mul_assoc, hBC, mul_one]
    _ = (B * D * C).charpoly := by rw [hAB]
    _ = D.charpoly := by rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hCB, one_mul]

attribute [local irreducible] decode binaryWord normal powerRows basisRows inverseRows

/-- A checked similarity preserves integer multiplicities in the characteristic polynomial. -/
theorem binaryWord_power_charpoly (k : Fin 6) :
    (binaryWord ^ (k.val + 1)).charpoly = sevenSpectrum (ZMod 2) 20 := by
  obtain ⟨hbi, hab⟩ := normal_certificate k
  exact (congrArg Matrix.charpoly (powers_rows k)).trans
    ((charpoly_of_certificate _ _ _ _ hbi (inverse_basis k) hab).trans charpoly_normal)

end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
