module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Arithmetic
import Mathlib.Tactic.FinCases

/-!
# Shared checked products for the 114 published words

These are certificates for the published words in FiniteIncidence/Words.lean.
Literal binary rows and word decompositions are untrusted witnesses. Each
product is checked by kernel reduction through packedRow_spec, and all group
claims are transferred to the actual matrix subgroup. Source context:
Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528; Aschbacher (1986).
See Obstructions/source/README.md for the certificate construction.
-/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate

def wordMatrix000 : QuotientMatrix := quotientDecode #v[1883, 1608, 3536, 2152, 3535, 1974, 425, 136, 197, 1627, 904, 2201]

private theorem wordMatrix000_product : wordMatrix000 = matrixYInv * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix000_expansion : wordMatrix000 = matrixYInv * (matrixX) := by
  simp only [wordMatrix000_product]

def wordMatrix001 : QuotientMatrix := quotientDecode #v[559, 2962, 670, 3040, 2920, 3387, 2405, 3305, 685, 2563, 3034, 2687]

private theorem wordMatrix001_product : wordMatrix001 = matrixY * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix001_expansion : wordMatrix001 = matrixY * (matrixX) := by
  simp only [wordMatrix001_product]

def wordMatrix002 : QuotientMatrix := quotientDecode #v[804, 860, 3564, 1473, 1607, 194, 2736, 1801, 1341, 393, 4007, 1073]

private theorem wordMatrix002_product : wordMatrix002 = wordMatrix000 * wordMatrix001 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix002_expansion : wordMatrix002 = matrixYInv * (matrixX * (matrixY * (matrixX))) := by
  simp only [wordMatrix002_product, wordMatrix000_expansion, wordMatrix001_expansion, mul_assoc]

def wordMatrix003 : QuotientMatrix := quotientDecode #v[1350, 1288, 2284, 2192, 112, 2262, 1224, 693, 902, 4049, 3273, 441]

private theorem wordMatrix003_product : wordMatrix003 = wordMatrix001 * wordMatrix000 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix003_expansion : wordMatrix003 = matrixY * (matrixX * (matrixYInv * (matrixX))) := by
  simp only [wordMatrix003_product, wordMatrix001_expansion, wordMatrix000_expansion, mul_assoc]

def wordMatrix004 : QuotientMatrix := quotientDecode #v[3181, 2195, 33, 3188, 3954, 885, 1147, 3400, 723, 3301, 998, 297]

private theorem wordMatrix004_product : wordMatrix004 = wordMatrix002 * wordMatrix003 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix004_expansion : wordMatrix004 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix004_product, wordMatrix002_expansion, wordMatrix003_expansion, mul_assoc]

def wordMatrix005 : QuotientMatrix := quotientDecode #v[1529, 2029, 3864, 2706, 3094, 2566, 784, 2067, 3674, 1221, 3266, 447]

private theorem wordMatrix005_product : wordMatrix005 = wordMatrix004 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix005_expansion : wordMatrix005 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix005_product, wordMatrix004_expansion, mul_assoc]

def wordMatrix006 : QuotientMatrix := quotientDecode #v[2043, 3778, 3950, 2662, 3439, 1798, 3133, 221, 128, 2497, 3143, 3977]

private theorem wordMatrix006_product : wordMatrix006 = wordMatrix001 * wordMatrix001 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix006_expansion : wordMatrix006 = matrixY * (matrixX * (matrixY * (matrixX))) := by
  simp only [wordMatrix006_product, wordMatrix001_expansion, mul_assoc]

def wordMatrix007 : QuotientMatrix := quotientDecode #v[208, 2093, 2686, 3295, 1092, 1194, 2900, 892, 221, 1042, 2468, 1999]

private theorem wordMatrix007_product : wordMatrix007 = wordMatrix006 * wordMatrix006 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix007_expansion : wordMatrix007 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix007_product, wordMatrix006_expansion, mul_assoc]

def wordMatrix008 : QuotientMatrix := quotientDecode #v[11, 3090, 1850, 1774, 3678, 1151, 2248, 2272, 2986, 206, 3710, 2797]

private theorem wordMatrix008_product : wordMatrix008 = wordMatrix000 * wordMatrix000 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix008_expansion : wordMatrix008 = matrixYInv * (matrixX * (matrixYInv * (matrixX))) := by
  simp only [wordMatrix008_product, wordMatrix000_expansion, mul_assoc]

def wordMatrix009 : QuotientMatrix := quotientDecode #v[863, 99, 3019, 1450, 151, 1570, 2319, 1135, 1463, 1834, 1937, 3933]

private theorem wordMatrix009_product : wordMatrix009 = wordMatrix008 * wordMatrix006 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix009_expansion : wordMatrix009 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix009_product, wordMatrix008_expansion, wordMatrix006_expansion, mul_assoc]

def wordMatrix010 : QuotientMatrix := quotientDecode #v[3575, 1089, 2511, 2150, 1365, 21, 3987, 838, 201, 1893, 876, 1329]

private theorem wordMatrix010_product : wordMatrix010 = wordMatrix007 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix010_expansion : wordMatrix010 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix010_product, wordMatrix007_expansion, wordMatrix009_expansion, mul_assoc]

def wordMatrix011 : QuotientMatrix := quotientDecode #v[4001, 1118, 3266, 6, 3718, 4058, 761, 2514, 2009, 2945, 3785, 3792]

private theorem wordMatrix011_product : wordMatrix011 = wordMatrix005 * wordMatrix010 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix011_expansion : wordMatrix011 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix011_product, wordMatrix005_expansion, wordMatrix010_expansion, mul_assoc]

def wordMatrix012 : QuotientMatrix := quotientDecode #v[342, 1697, 359, 571, 1620, 4010, 2753, 3040, 2096, 3323, 691, 1961]

private theorem wordMatrix012_product : wordMatrix012 = wordMatrix003 * wordMatrix006 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix012_expansion : wordMatrix012 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix012_product, wordMatrix003_expansion, wordMatrix006_expansion, mul_assoc]

def wordMatrix013 : QuotientMatrix := quotientDecode #v[1589, 1224, 1525, 3740, 977, 2505, 3411, 3099, 2472, 3869, 289, 989]

private theorem wordMatrix013_product : wordMatrix013 = wordMatrix012 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix013_expansion : wordMatrix013 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY)))))))) := by
  simp only [wordMatrix013_product, wordMatrix012_expansion, mul_assoc]

def wordMatrix014 : QuotientMatrix := quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960]

private theorem wordMatrix014_product : wordMatrix014 = wordMatrix011 * wordMatrix013 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix014_expansion : wordMatrix014 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix014_product, wordMatrix011_expansion, wordMatrix013_expansion, mul_assoc]

def wordMatrix015 : QuotientMatrix := quotientDecode #v[3206, 1211, 3440, 3942, 2623, 3655, 3856, 4070, 513, 1665, 1781, 3641]

private theorem wordMatrix015_product : wordMatrix015 = matrixX * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix015_expansion : wordMatrix015 = matrixX * (matrixY) := by
  simp only [wordMatrix015_product]

def wordMatrix016 : QuotientMatrix := quotientDecode #v[1977, 940, 2835, 693, 1772, 1021, 1719, 685, 506, 3663, 2609, 2138]

private theorem wordMatrix016_product : wordMatrix016 = matrixX * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix016_expansion : wordMatrix016 = matrixX * (matrixYInv) := by
  simp only [wordMatrix016_product]

def wordMatrix017 : QuotientMatrix := quotientDecode #v[2169, 2861, 55, 43, 3767, 1429, 2866, 646, 2550, 362, 2527, 3129]

private theorem wordMatrix017_product : wordMatrix017 = wordMatrix015 * wordMatrix016 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix017_expansion : wordMatrix017 = matrixX * (matrixY * (matrixX * (matrixYInv))) := by
  simp only [wordMatrix017_product, wordMatrix015_expansion, wordMatrix016_expansion, mul_assoc]

def wordMatrix018 : QuotientMatrix := quotientDecode #v[1844, 1859, 1302, 1369, 2623, 161, 3268, 256, 488, 1824, 1213, 2328]

private theorem wordMatrix018_product : wordMatrix018 = wordMatrix016 * wordMatrix016 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix018_expansion : wordMatrix018 = matrixX * (matrixYInv * (matrixX * (matrixYInv))) := by
  simp only [wordMatrix018_product, wordMatrix016_expansion, mul_assoc]

def wordMatrix019 : QuotientMatrix := quotientDecode #v[3375, 2058, 4095, 1423, 1146, 3144, 525, 1141, 3583, 3991, 3891, 1366]

private theorem wordMatrix019_product : wordMatrix019 = wordMatrix017 * wordMatrix018 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix019_expansion : wordMatrix019 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix019_product, wordMatrix017_expansion, wordMatrix018_expansion, mul_assoc]

def wordMatrix020 : QuotientMatrix := quotientDecode #v[2571, 1847, 2235, 3305, 3283, 3742, 3751, 2480, 3410, 2934, 70, 203]

private theorem wordMatrix020_product : wordMatrix020 = wordMatrix016 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix020_expansion : wordMatrix020 = matrixX * (matrixYInv * (matrixX * (matrixY))) := by
  simp only [wordMatrix020_product, wordMatrix016_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix021 : QuotientMatrix := quotientDecode #v[3628, 2306, 1762, 405, 433, 908, 252, 3179, 696, 4015, 40, 2763]

private theorem wordMatrix021_product : wordMatrix021 = wordMatrix020 * wordMatrix017 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix021_expansion : wordMatrix021 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix021_product, wordMatrix020_expansion, wordMatrix017_expansion, mul_assoc]

def wordMatrix022 : QuotientMatrix := quotientDecode #v[2958, 604, 2311, 3746, 2686, 2954, 1780, 2599, 1704, 3042, 743, 3133]

private theorem wordMatrix022_product : wordMatrix022 = wordMatrix019 * wordMatrix021 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix022_expansion : wordMatrix022 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix022_product, wordMatrix019_expansion, wordMatrix021_expansion, mul_assoc]

def wordMatrix023 : QuotientMatrix := quotientDecode #v[3809, 2608, 421, 1232, 1771, 1040, 1651, 2870, 2567, 788, 1292, 2517]

private theorem wordMatrix023_product : wordMatrix023 = wordMatrix015 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix023_expansion : wordMatrix023 = matrixX * (matrixY * (matrixX * (matrixY))) := by
  simp only [wordMatrix023_product, wordMatrix015_expansion, mul_assoc]

def wordMatrix024 : QuotientMatrix := quotientDecode #v[3905, 3773, 629, 1442, 2462, 455, 57, 2567, 1922, 2063, 1877, 489]

private theorem wordMatrix024_product : wordMatrix024 = wordMatrix018 * wordMatrix023 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix024_expansion : wordMatrix024 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix024_product, wordMatrix018_expansion, wordMatrix023_expansion, mul_assoc]

def wordMatrix025 : QuotientMatrix := quotientDecode #v[1839, 3818, 1912, 763, 2780, 349, 146, 27, 292, 2563, 2556, 3951]

private theorem wordMatrix025_product : wordMatrix025 = wordMatrix024 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix025_expansion : wordMatrix025 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix025_product, wordMatrix024_expansion, wordMatrix019_expansion, mul_assoc]

def wordMatrix026 : QuotientMatrix := quotientDecode #v[3898, 1486, 246, 828, 1302, 2114, 3983, 2700, 66, 2934, 1386, 4030]

private theorem wordMatrix026_product : wordMatrix026 = wordMatrix022 * wordMatrix025 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix026_expansion : wordMatrix026 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix026_product, wordMatrix022_expansion, wordMatrix025_expansion, mul_assoc]

def wordMatrix027 : QuotientMatrix := quotientDecode #v[1147, 2389, 2113, 1770, 3659, 1110, 1194, 2294, 3139, 3159, 388, 1686]

private theorem wordMatrix027_product : wordMatrix027 = wordMatrix017 * wordMatrix017 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix027_expansion : wordMatrix027 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix027_product, wordMatrix017_expansion, mul_assoc]

def wordMatrix028 : QuotientMatrix := quotientDecode #v[2758, 2273, 3503, 1304, 1542, 2577, 3209, 892, 4065, 2222, 151, 3174]

private theorem wordMatrix028_product : wordMatrix028 = wordMatrix027 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix028_expansion : wordMatrix028 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))) := by
  simp only [wordMatrix028_product, wordMatrix027_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix029 : QuotientMatrix := quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155]

private theorem wordMatrix029_product : wordMatrix029 = wordMatrix026 * wordMatrix028 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix029_expansion : wordMatrix029 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix029_product, wordMatrix026_expansion, wordMatrix028_expansion, mul_assoc]

def wordMatrix030 : QuotientMatrix := quotientDecode #v[2807, 1759, 1479, 1825, 3853, 346, 3115, 3770, 2026, 3566, 2930, 4011]

private theorem wordMatrix030_product : wordMatrix030 = wordMatrix008 * wordMatrix008 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix030_expansion : wordMatrix030 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix030_product, wordMatrix008_expansion, mul_assoc]

def wordMatrix031 : QuotientMatrix := quotientDecode #v[3111, 489, 3289, 712, 3265, 3389, 2352, 2946, 881, 3740, 4080, 2638]

private theorem wordMatrix031_product : wordMatrix031 = wordMatrix030 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix031_expansion : wordMatrix031 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix031_product, wordMatrix030_expansion, wordMatrix004_expansion, mul_assoc]

def wordMatrix032 : QuotientMatrix := quotientDecode #v[1588, 826, 3950, 3155, 745, 4019, 2232, 1342, 2220, 394, 606, 3982]

private theorem wordMatrix032_product : wordMatrix032 = wordMatrix003 * wordMatrix008 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix032_expansion : wordMatrix032 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix032_product, wordMatrix003_expansion, wordMatrix008_expansion, mul_assoc]

def wordMatrix033 : QuotientMatrix := quotientDecode #v[4050, 3415, 2439, 1884, 558, 1438, 3809, 407, 3051, 1727, 1863, 3448]

private theorem wordMatrix033_product : wordMatrix033 = wordMatrix004 * wordMatrix032 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix033_expansion : wordMatrix033 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix033_product, wordMatrix004_expansion, wordMatrix032_expansion, mul_assoc]

def wordMatrix034 : QuotientMatrix := quotientDecode #v[1187, 2445, 4073, 3733, 2715, 1901, 291, 3308, 3031, 482, 4013, 1706]

private theorem wordMatrix034_product : wordMatrix034 = wordMatrix031 * wordMatrix033 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix034_expansion : wordMatrix034 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix034_product, wordMatrix031_expansion, wordMatrix033_expansion, mul_assoc]

def wordMatrix035 : QuotientMatrix := quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184]

private theorem wordMatrix035_product : wordMatrix035 = wordMatrix034 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix035_expansion : wordMatrix035 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix035_product, wordMatrix034_expansion, mul_assoc]

def wordMatrix036 : QuotientMatrix := quotientDecode #v[3738, 3931, 359, 1407, 3125, 383, 2015, 3789, 3341, 2040, 202, 596]

private theorem wordMatrix036_product : wordMatrix036 = wordMatrix003 * wordMatrix002 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix036_expansion : wordMatrix036 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix036_product, wordMatrix003_expansion, wordMatrix002_expansion, mul_assoc]

def wordMatrix037 : QuotientMatrix := quotientDecode #v[2430, 1778, 884, 42, 1470, 2904, 548, 951, 2850, 2705, 879, 2831]

private theorem wordMatrix037_product : wordMatrix037 = wordMatrix036 * wordMatrix030 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix037_expansion : wordMatrix037 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix037_product, wordMatrix036_expansion, wordMatrix030_expansion, mul_assoc]

def wordMatrix038 : QuotientMatrix := quotientDecode #v[1465, 3725, 2827, 2084, 3481, 3015, 3145, 2378, 467, 1736, 3419, 970]

private theorem wordMatrix038_product : wordMatrix038 = wordMatrix008 * wordMatrix002 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix038_expansion : wordMatrix038 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix038_product, wordMatrix008_expansion, wordMatrix002_expansion, mul_assoc]

def wordMatrix039 : QuotientMatrix := quotientDecode #v[2202, 3739, 695, 3600, 2585, 2431, 3594, 3619, 3596, 3663, 2975, 1880]

private theorem wordMatrix039_product : wordMatrix039 = wordMatrix007 * wordMatrix038 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix039_expansion : wordMatrix039 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix039_product, wordMatrix007_expansion, wordMatrix038_expansion, mul_assoc]

def wordMatrix040 : QuotientMatrix := quotientDecode #v[1540, 2052, 3992, 2548, 2794, 3352, 1415, 2480, 255, 1463, 3472, 3517]

private theorem wordMatrix040_product : wordMatrix040 = wordMatrix037 * wordMatrix039 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix040_expansion : wordMatrix040 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix040_product, wordMatrix037_expansion, wordMatrix039_expansion, mul_assoc]

def wordMatrix041 : QuotientMatrix := quotientDecode #v[2427, 150, 335, 180, 732, 3315, 464, 3598, 1817, 721, 1386, 2742]

private theorem wordMatrix041_product : wordMatrix041 = wordMatrix008 * wordMatrix000 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix041_expansion : wordMatrix041 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))) := by
  simp only [wordMatrix041_product, wordMatrix008_expansion, wordMatrix000_expansion, mul_assoc]

def wordMatrix042 : QuotientMatrix := quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100]

private theorem wordMatrix042_product : wordMatrix042 = wordMatrix040 * wordMatrix041 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix042_expansion : wordMatrix042 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix042_product, wordMatrix040_expansion, wordMatrix041_expansion, mul_assoc]

def wordMatrix043 : QuotientMatrix := quotientDecode #v[297, 3355, 3488, 2012, 4076, 546, 3324, 2203, 1117, 3520, 2819, 469]

private theorem wordMatrix043_product : wordMatrix043 = wordMatrix002 * wordMatrix006 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix043_expansion : wordMatrix043 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix043_product, wordMatrix002_expansion, wordMatrix006_expansion, mul_assoc]

def wordMatrix044 : QuotientMatrix := quotientDecode #v[2726, 2997, 2833, 2082, 2961, 801, 3931, 2084, 1502, 3307, 3744, 880]

private theorem wordMatrix044_product : wordMatrix044 = wordMatrix036 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix044_expansion : wordMatrix044 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix044_product, wordMatrix036_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix045 : QuotientMatrix := quotientDecode #v[1430, 1274, 3617, 378, 3212, 1443, 1562, 247, 1801, 3985, 3250, 3790]

private theorem wordMatrix045_product : wordMatrix045 = wordMatrix006 * wordMatrix002 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix045_expansion : wordMatrix045 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix045_product, wordMatrix006_expansion, wordMatrix002_expansion, mul_assoc]

def wordMatrix046 : QuotientMatrix := quotientDecode #v[3355, 1776, 3544, 3516, 3536, 3971, 2607, 143, 198, 777, 3934, 161]

private theorem wordMatrix046_product : wordMatrix046 = wordMatrix045 * wordMatrix045 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix046_expansion : wordMatrix046 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix046_product, wordMatrix045_expansion, mul_assoc]

def wordMatrix047 : QuotientMatrix := quotientDecode #v[1932, 369, 933, 2514, 810, 343, 3480, 762, 3708, 3211, 1018, 2995]

private theorem wordMatrix047_product : wordMatrix047 = wordMatrix044 * wordMatrix046 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix047_expansion : wordMatrix047 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix047_product, wordMatrix044_expansion, wordMatrix046_expansion, mul_assoc]

def wordMatrix048 : QuotientMatrix := quotientDecode #v[1696, 1835, 396, 2451, 1653, 1060, 3829, 4029, 1958, 3600, 1416, 4077]

private theorem wordMatrix048_product : wordMatrix048 = wordMatrix000 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix048_expansion : wordMatrix048 = matrixYInv * (matrixX * (matrixY)) := by
  simp only [wordMatrix048_product, wordMatrix000_expansion, mul_assoc]

def wordMatrix049 : QuotientMatrix := quotientDecode #v[2972, 3490, 1283, 2141, 810, 3873, 3480, 945, 206, 3520, 1047, 2620]

private theorem wordMatrix049_product : wordMatrix049 = wordMatrix047 * wordMatrix048 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix049_expansion : wordMatrix049 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix049_product, wordMatrix047_expansion, wordMatrix048_expansion, mul_assoc]

def wordMatrix050 : QuotientMatrix := quotientDecode #v[1635, 2015, 3950, 892, 3182, 2640, 548, 2152, 774, 620, 1755, 1091]

private theorem wordMatrix050_product : wordMatrix050 = wordMatrix003 * wordMatrix003 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix050_expansion : wordMatrix050 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix050_product, wordMatrix003_expansion, mul_assoc]

def wordMatrix051 : QuotientMatrix := quotientDecode #v[3559, 1015, 75, 3438, 1903, 3096, 2409, 2094, 2665, 4045, 2027, 87]

private theorem wordMatrix051_product : wordMatrix051 = wordMatrix032 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix051_expansion : wordMatrix051 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix051_product, wordMatrix032_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix052 : QuotientMatrix := quotientDecode #v[2081, 3110, 2746, 1527, 3419, 3130, 2274, 1023, 3626, 1455, 2123, 1108]

private theorem wordMatrix052_product : wordMatrix052 = wordMatrix002 * wordMatrix008 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix052_expansion : wordMatrix052 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix052_product, wordMatrix002_expansion, wordMatrix008_expansion, mul_assoc]

def wordMatrix053 : QuotientMatrix := quotientDecode #v[1545, 3639, 2313, 78, 1648, 4067, 3713, 4041, 3200, 1612, 3691, 1889]

private theorem wordMatrix053_product : wordMatrix053 = wordMatrix052 * wordMatrix032 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix053_expansion : wordMatrix053 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix053_product, wordMatrix052_expansion, wordMatrix032_expansion, mul_assoc]

def wordMatrix054 : QuotientMatrix := quotientDecode #v[2582, 800, 1777, 920, 1212, 3892, 3268, 4082, 1544, 3520, 636, 2502]

private theorem wordMatrix054_product : wordMatrix054 = wordMatrix051 * wordMatrix053 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix054_expansion : wordMatrix054 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix054_product, wordMatrix051_expansion, wordMatrix053_expansion, mul_assoc]

def wordMatrix055 : QuotientMatrix := quotientDecode #v[2699, 3655, 1268, 3733, 1019, 3976, 64, 708, 4064, 4014, 2717, 581]

private theorem wordMatrix055_product : wordMatrix055 = wordMatrix054 * wordMatrix006 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix055_expansion : wordMatrix055 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix055_product, wordMatrix054_expansion, wordMatrix006_expansion, mul_assoc]

def wordMatrix056 : QuotientMatrix := quotientDecode #v[2160, 121, 3290, 1917, 3348, 5, 896, 182, 3591, 2635, 1191, 2047]

private theorem wordMatrix056_product : wordMatrix056 = wordMatrix052 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix056_expansion : wordMatrix056 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix056_product, wordMatrix052_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix057 : QuotientMatrix := quotientDecode #v[2458, 110, 3069, 1031, 2314, 3813, 1076, 3574, 1814, 1233, 1405, 2566]

private theorem wordMatrix057_product : wordMatrix057 = wordMatrix002 * wordMatrix002 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix057_expansion : wordMatrix057 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))) := by
  simp only [wordMatrix057_product, wordMatrix002_expansion, mul_assoc]

def wordMatrix058 : QuotientMatrix := quotientDecode #v[2295, 805, 3568, 1297, 1781, 3879, 2846, 2466, 2683, 3126, 3036, 2018]

private theorem wordMatrix058_product : wordMatrix058 = wordMatrix009 * wordMatrix057 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix058_expansion : wordMatrix058 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix058_product, wordMatrix009_expansion, wordMatrix057_expansion, mul_assoc]

def wordMatrix059 : QuotientMatrix := quotientDecode #v[1326, 3882, 3651, 3915, 3392, 1287, 4079, 3749, 1578, 3593, 2939, 1484]

private theorem wordMatrix059_product : wordMatrix059 = wordMatrix056 * wordMatrix058 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix059_expansion : wordMatrix059 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix059_product, wordMatrix056_expansion, wordMatrix058_expansion, mul_assoc]

def wordMatrix060 : QuotientMatrix := quotientDecode #v[804, 2513, 666, 1423, 2988, 1401, 3703, 3256, 2166, 2277, 2717, 3169]

private theorem wordMatrix060_product : wordMatrix060 = wordMatrix059 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix060_expansion : wordMatrix060 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix060_product, wordMatrix059_expansion, mul_assoc]

def wordMatrix061 : QuotientMatrix := quotientDecode #v[1624, 3089, 1590, 1442, 3087, 1786, 1975, 1505, 2059, 1767, 683, 3831]

private theorem wordMatrix061_product : wordMatrix061 = wordMatrix009 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix061_expansion : wordMatrix061 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix061_product, wordMatrix009_expansion, mul_assoc]

def wordMatrix062 : QuotientMatrix := quotientDecode #v[241, 3830, 1821, 3989, 3494, 2366, 3206, 3663, 1301, 3379, 421, 3389]

private theorem wordMatrix062_product : wordMatrix062 = wordMatrix045 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix062_expansion : wordMatrix062 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix062_product, wordMatrix045_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix063 : QuotientMatrix := quotientDecode #v[547, 463, 485, 3383, 2583, 2980, 2638, 4022, 3247, 3707, 3024, 3808]

private theorem wordMatrix063_product : wordMatrix063 = wordMatrix061 * wordMatrix062 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix063_expansion : wordMatrix063 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix063_product, wordMatrix061_expansion, wordMatrix062_expansion, mul_assoc]

def wordMatrix064 : QuotientMatrix := quotientDecode #v[928, 2232, 2284, 823, 1305, 1930, 1462, 58, 2870, 118, 4062, 1229]

private theorem wordMatrix064_product : wordMatrix064 = wordMatrix003 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix064_expansion : wordMatrix064 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))) := by
  simp only [wordMatrix064_product, wordMatrix003_expansion, mul_assoc]

def wordMatrix065 : QuotientMatrix := quotientDecode #v[3300, 3705, 636, 322, 598, 209, 622, 686, 3168, 1135, 3864, 2403]

private theorem wordMatrix065_product : wordMatrix065 = wordMatrix063 * wordMatrix064 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix065_expansion : wordMatrix065 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix065_product, wordMatrix063_expansion, wordMatrix064_expansion, mul_assoc]

def wordMatrix066 : QuotientMatrix := quotientDecode #v[2270, 2056, 1440, 2247, 877, 149, 3924, 3858, 2581, 777, 3003, 1529]

private theorem wordMatrix066_product : wordMatrix066 = wordMatrix008 * wordMatrix003 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix066_expansion : wordMatrix066 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix066_product, wordMatrix008_expansion, wordMatrix003_expansion, mul_assoc]

def wordMatrix067 : QuotientMatrix := quotientDecode #v[1082, 2384, 2123, 1870, 1018, 2254, 3846, 964, 244, 1007, 1127, 2713]

private theorem wordMatrix067_product : wordMatrix067 = wordMatrix004 * wordMatrix066 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix067_expansion : wordMatrix067 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix067_product, wordMatrix004_expansion, wordMatrix066_expansion, mul_assoc]

def wordMatrix068 : QuotientMatrix := quotientDecode #v[1508, 2151, 3718, 3516, 3651, 3634, 3949, 4009, 2272, 356, 1912, 498]

private theorem wordMatrix068_product : wordMatrix068 = wordMatrix006 * wordMatrix008 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix068_expansion : wordMatrix068 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix068_product, wordMatrix006_expansion, wordMatrix008_expansion, mul_assoc]

def wordMatrix069 : QuotientMatrix := quotientDecode #v[687, 2183, 33, 448, 1493, 2352, 2114, 3817, 1055, 337, 3868, 3585]

private theorem wordMatrix069_product : wordMatrix069 = wordMatrix068 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix069_expansion : wordMatrix069 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix069_product, wordMatrix068_expansion, wordMatrix009_expansion, mul_assoc]

def wordMatrix070 : QuotientMatrix := quotientDecode #v[2750, 1929, 3499, 2934, 1607, 460, 3317, 964, 2671, 284, 1127, 1795]

private theorem wordMatrix070_product : wordMatrix070 = wordMatrix067 * wordMatrix069 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix070_expansion : wordMatrix070 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix070_product, wordMatrix067_expansion, wordMatrix069_expansion, mul_assoc]

def wordMatrix071 : QuotientMatrix := quotientDecode #v[1975, 953, 1642, 2180, 2601, 1101, 806, 405, 3612, 3591, 2208, 3595]

private theorem wordMatrix071_product : wordMatrix071 = wordMatrix000 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix071_expansion : wordMatrix071 = matrixYInv * (matrixX * (matrixYInv)) := by
  simp only [wordMatrix071_product, wordMatrix000_expansion, mul_assoc]

def wordMatrix072 : QuotientMatrix := quotientDecode #v[682, 1565, 485, 1665, 2021, 577, 2977, 1218, 3463, 2779, 3503, 3253]

private theorem wordMatrix072_product : wordMatrix072 = wordMatrix070 * wordMatrix071 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix072_expansion : wordMatrix072 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix072_product, wordMatrix070_expansion, wordMatrix071_expansion, mul_assoc]

def wordMatrix073 : QuotientMatrix := quotientDecode #v[2752, 2960, 25, 4029, 934, 3413, 1439, 2591, 3190, 4059, 3558, 3396]

private theorem wordMatrix073_product : wordMatrix073 = wordMatrix020 * wordMatrix023 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix073_expansion : wordMatrix073 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix073_product, wordMatrix020_expansion, wordMatrix023_expansion, mul_assoc]

def wordMatrix074 : QuotientMatrix := quotientDecode #v[2646, 2341, 1412, 3582, 1337, 3946, 3173, 2550, 1532, 1238, 2078, 2899]

private theorem wordMatrix074_product : wordMatrix074 = wordMatrix018 * wordMatrix017 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix074_expansion : wordMatrix074 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix074_product, wordMatrix018_expansion, wordMatrix017_expansion, mul_assoc]

def wordMatrix075 : QuotientMatrix := quotientDecode #v[2582, 1718, 657, 1006, 2839, 63, 2596, 437, 2522, 3136, 233, 3920]

private theorem wordMatrix075_product : wordMatrix075 = wordMatrix073 * wordMatrix074 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix075_expansion : wordMatrix075 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix075_product, wordMatrix073_expansion, wordMatrix074_expansion, mul_assoc]

def wordMatrix076 : QuotientMatrix := quotientDecode #v[212, 1190, 619, 838, 3030, 3714, 1456, 1819, 2905, 2529, 1306, 3369]

private theorem wordMatrix076_product : wordMatrix076 = wordMatrix023 * wordMatrix018 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix076_expansion : wordMatrix076 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix076_product, wordMatrix023_expansion, wordMatrix018_expansion, mul_assoc]

def wordMatrix077 : QuotientMatrix := quotientDecode #v[1900, 3906, 1935, 1041, 884, 3474, 2061, 951, 2041, 1668, 2520, 1043]

private theorem wordMatrix077_product : wordMatrix077 = wordMatrix017 * wordMatrix023 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix077_expansion : wordMatrix077 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix077_product, wordMatrix017_expansion, wordMatrix023_expansion, mul_assoc]

def wordMatrix078 : QuotientMatrix := quotientDecode #v[3905, 3888, 3876, 445, 1389, 1978, 880, 2030, 3434, 686, 1542, 1245]

private theorem wordMatrix078_product : wordMatrix078 = wordMatrix076 * wordMatrix077 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix078_expansion : wordMatrix078 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix078_product, wordMatrix076_expansion, wordMatrix077_expansion, mul_assoc]

def wordMatrix079 : QuotientMatrix := quotientDecode #v[778, 389, 3948, 3401, 289, 3135, 3821, 2102, 1737, 427, 3544, 2818]

private theorem wordMatrix079_product : wordMatrix079 = wordMatrix075 * wordMatrix078 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix079_expansion : wordMatrix079 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix079_product, wordMatrix075_expansion, wordMatrix078_expansion, mul_assoc]

def wordMatrix080 : QuotientMatrix := quotientDecode #v[2664, 424, 2787, 4070, 1653, 3581, 2386, 1636, 2204, 1417, 299, 1730]

private theorem wordMatrix080_product : wordMatrix080 = wordMatrix020 * wordMatrix020 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix080_expansion : wordMatrix080 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix080_product, wordMatrix020_expansion, mul_assoc]

def wordMatrix081 : QuotientMatrix := quotientDecode #v[212, 1048, 731, 1569, 1788, 3877, 993, 902, 1469, 2120, 992, 2783]

private theorem wordMatrix081_product : wordMatrix081 = wordMatrix015 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix081_expansion : wordMatrix081 = matrixX * (matrixY * (matrixX)) := by
  simp only [wordMatrix081_product, wordMatrix015_expansion, mul_assoc]

def wordMatrix082 : QuotientMatrix := quotientDecode #v[2162, 3903, 2329, 3403, 927, 274, 3687, 1463, 2911, 814, 2165, 4055]

private theorem wordMatrix082_product : wordMatrix082 = wordMatrix080 * wordMatrix081 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix082_expansion : wordMatrix082 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))) := by
  simp only [wordMatrix082_product, wordMatrix080_expansion, wordMatrix081_expansion, mul_assoc]

def wordMatrix083 : QuotientMatrix := quotientDecode #v[2565, 3971, 1268, 1955, 575, 1584, 622, 2940, 1458, 1532, 2553, 2201]

private theorem wordMatrix083_product : wordMatrix083 = wordMatrix079 * wordMatrix082 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix083_expansion : wordMatrix083 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix083_product, wordMatrix079_expansion, wordMatrix082_expansion, mul_assoc]

def wordMatrix084 : QuotientMatrix := quotientDecode #v[2755, 1576, 1994, 3915, 1409, 2759, 917, 3402, 1871, 1717, 3891, 1058]

private theorem wordMatrix084_product : wordMatrix084 = wordMatrix017 * wordMatrix020 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix084_expansion : wordMatrix084 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix084_product, wordMatrix017_expansion, wordMatrix020_expansion, mul_assoc]

def wordMatrix085 : QuotientMatrix := quotientDecode #v[212, 1649, 1707, 3804, 2027, 1896, 3057, 1181, 3632, 1564, 53, 2690]

private theorem wordMatrix085_product : wordMatrix085 = wordMatrix023 * wordMatrix017 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix085_expansion : wordMatrix085 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix085_product, wordMatrix023_expansion, wordMatrix017_expansion, mul_assoc]

def wordMatrix086 : QuotientMatrix := quotientDecode #v[1367, 3997, 4056, 275, 2636, 1020, 3365, 2011, 3386, 1096, 1213, 300]

private theorem wordMatrix086_product : wordMatrix086 = wordMatrix084 * wordMatrix085 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix086_expansion : wordMatrix086 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix086_product, wordMatrix084_expansion, wordMatrix085_expansion, mul_assoc]

def wordMatrix087 : QuotientMatrix := quotientDecode #v[2169, 2106, 2661, 3746, 3916, 999, 1601, 2472, 4021, 3677, 2686, 1848]

private theorem wordMatrix087_product : wordMatrix087 = wordMatrix023 * wordMatrix023 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix087_expansion : wordMatrix087 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix087_product, wordMatrix023_expansion, mul_assoc]

def wordMatrix088 : QuotientMatrix := quotientDecode #v[406, 772, 1903, 2129, 1707, 3837, 1944, 2593, 1947, 554, 1340, 2128]

private theorem wordMatrix088_product : wordMatrix088 = wordMatrix087 * wordMatrix080 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix088_expansion : wordMatrix088 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix088_product, wordMatrix087_expansion, wordMatrix080_expansion, mul_assoc]

def wordMatrix089 : QuotientMatrix := quotientDecode #v[1641, 2815, 2974, 930, 732, 3936, 755, 348, 2548, 2805, 2531, 1624]

private theorem wordMatrix089_product : wordMatrix089 = wordMatrix086 * wordMatrix088 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix089_expansion : wordMatrix089 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix089_product, wordMatrix086_expansion, wordMatrix088_expansion, mul_assoc]

def wordMatrix090 : QuotientMatrix := quotientDecode #v[707, 1565, 2509, 410, 3678, 3355, 2610, 1336, 1478, 3520, 2740, 2621]

private theorem wordMatrix090_product : wordMatrix090 = wordMatrix089 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix090_expansion : wordMatrix090 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix090_product, wordMatrix089_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix091 : QuotientMatrix := quotientDecode #v[811, 213, 3891, 216, 335, 1267, 1404, 2263, 1682, 222, 1483, 3920]

private theorem wordMatrix091_product : wordMatrix091 = wordMatrix007 * wordMatrix066 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix091_expansion : wordMatrix091 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix091_product, wordMatrix007_expansion, wordMatrix066_expansion, mul_assoc]

def wordMatrix092 : QuotientMatrix := quotientDecode #v[2713, 3883, 3024, 3307, 2794, 2964, 155, 407, 571, 1041, 3123, 1088]

private theorem wordMatrix092_product : wordMatrix092 = wordMatrix043 * wordMatrix066 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix092_expansion : wordMatrix092 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix092_product, wordMatrix043_expansion, wordMatrix066_expansion, mul_assoc]

def wordMatrix093 : QuotientMatrix := quotientDecode #v[1255, 2735, 2709, 1805, 41, 2547, 2262, 452, 3188, 1014, 1629, 1064]

private theorem wordMatrix093_product : wordMatrix093 = wordMatrix091 * wordMatrix092 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix093_expansion : wordMatrix093 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix093_product, wordMatrix091_expansion, wordMatrix092_expansion, mul_assoc]

def wordMatrix094 : QuotientMatrix := quotientDecode #v[266, 2929, 2988, 1221, 666, 1879, 4019, 3256, 320, 2629, 2553, 3311]

private theorem wordMatrix094_product : wordMatrix094 = wordMatrix093 * wordMatrix008 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix094_expansion : wordMatrix094 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix094_product, wordMatrix093_expansion, wordMatrix008_expansion, mul_assoc]

def wordMatrix095 : QuotientMatrix := quotientDecode #v[94, 1445, 3123, 1390, 142, 1711, 81, 2951, 2461, 2152, 879, 2065]

private theorem wordMatrix095_product : wordMatrix095 = wordMatrix074 * wordMatrix085 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix095_expansion : wordMatrix095 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix095_product, wordMatrix074_expansion, wordMatrix085_expansion, mul_assoc]

def wordMatrix096 : QuotientMatrix := quotientDecode #v[2838, 3466, 1960, 685, 2601, 1718, 3653, 878, 3573, 3039, 3729, 2282]

private theorem wordMatrix096_product : wordMatrix096 = wordMatrix020 * wordMatrix018 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix096_expansion : wordMatrix096 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix096_product, wordMatrix020_expansion, wordMatrix018_expansion, mul_assoc]

def wordMatrix097 : QuotientMatrix := quotientDecode #v[170, 3202, 1191, 4003, 1815, 741, 1122, 2501, 315, 2658, 33, 3537]

private theorem wordMatrix097_product : wordMatrix097 = wordMatrix085 * wordMatrix096 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix097_expansion : wordMatrix097 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix097_product, wordMatrix085_expansion, wordMatrix096_expansion, mul_assoc]

def wordMatrix098 : QuotientMatrix := quotientDecode #v[1267, 3639, 1066, 27, 3651, 1615, 991, 1986, 2454, 1269, 2802, 2668]

private theorem wordMatrix098_product : wordMatrix098 = wordMatrix095 * wordMatrix097 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix098_expansion : wordMatrix098 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix098_product, wordMatrix095_expansion, wordMatrix097_expansion, mul_assoc]

def wordMatrix099 : QuotientMatrix := quotientDecode #v[3194, 3264, 598, 3132, 2462, 3274, 801, 1802, 3573, 975, 1762, 1799]

private theorem wordMatrix099_product : wordMatrix099 = wordMatrix023 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix099_expansion : wordMatrix099 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))) := by
  simp only [wordMatrix099_product, wordMatrix023_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix100 : QuotientMatrix := quotientDecode #v[1831, 1426, 2772, 1304, 433, 2268, 3423, 51, 2800, 2481, 2423, 1353]

private theorem wordMatrix100_product : wordMatrix100 = wordMatrix098 * wordMatrix099 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix100_expansion : wordMatrix100 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix100_product, wordMatrix098_expansion, wordMatrix099_expansion, mul_assoc]

def wordMatrix101 : QuotientMatrix := quotientDecode #v[2169, 2544, 2252, 2946, 876, 3221, 2790, 2862, 3642, 588, 2374, 1261]

private theorem wordMatrix101_product : wordMatrix101 = wordMatrix023 * wordMatrix020 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix101_expansion : wordMatrix101 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix101_product, wordMatrix023_expansion, wordMatrix020_expansion, mul_assoc]

def wordMatrix102 : QuotientMatrix := quotientDecode #v[406, 2784, 3313, 3099, 3263, 1907, 2763, 647, 1958, 2526, 3143, 3213]

private theorem wordMatrix102_product : wordMatrix102 = wordMatrix101 * wordMatrix080 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix102_expansion : wordMatrix102 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix102_product, wordMatrix101_expansion, wordMatrix080_expansion, mul_assoc]

def wordMatrix103 : QuotientMatrix := quotientDecode #v[3957, 2409, 3208, 1403, 679, 2688, 2751, 3155, 851, 3071, 3244, 3104]

private theorem wordMatrix103_product : wordMatrix103 = wordMatrix019 * wordMatrix073 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix103_expansion : wordMatrix103 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix103_product, wordMatrix019_expansion, wordMatrix073_expansion, mul_assoc]

def wordMatrix104 : QuotientMatrix := quotientDecode #v[2118, 2995, 306, 332, 2839, 132, 596, 3384, 1842, 2978, 167, 2649]

private theorem wordMatrix104_product : wordMatrix104 = wordMatrix102 * wordMatrix103 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix104_expansion : wordMatrix104 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix104_product, wordMatrix102_expansion, wordMatrix103_expansion, mul_assoc]

def wordMatrix105 : QuotientMatrix := quotientDecode #v[3787, 1991, 4046, 20, 3128, 157, 3935, 1622, 1668, 2651, 4085, 3152]

private theorem wordMatrix105_product : wordMatrix105 = wordMatrix096 * wordMatrix096 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix105_expansion : wordMatrix105 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix105_product, wordMatrix096_expansion, mul_assoc]

def wordMatrix106 : QuotientMatrix := quotientDecode #v[2866, 38, 1722, 2905, 706, 460, 958, 1817, 3693, 3055, 619, 271]

private theorem wordMatrix106_product : wordMatrix106 = wordMatrix096 * wordMatrix024 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix106_expansion : wordMatrix106 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix106_product, wordMatrix096_expansion, wordMatrix024_expansion, mul_assoc]

def wordMatrix107 : QuotientMatrix := quotientDecode #v[3169, 3808, 3972, 1144, 2867, 778, 365, 3684, 2087, 3025, 3271, 536]

private theorem wordMatrix107_product : wordMatrix107 = wordMatrix105 * wordMatrix106 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix107_expansion : wordMatrix107 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix107_product, wordMatrix105_expansion, wordMatrix106_expansion, mul_assoc]

def wordMatrix108 : QuotientMatrix := quotientDecode #v[152, 3011, 1120, 2850, 1771, 3756, 2735, 637, 1185, 672, 2423, 2582]

private theorem wordMatrix108_product : wordMatrix108 = wordMatrix107 * wordMatrix016 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix108_expansion : wordMatrix108 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix108_product, wordMatrix107_expansion, wordMatrix016_expansion, mul_assoc]

def wordMatrix109 : QuotientMatrix := quotientDecode #v[3464, 2722, 2936, 3862, 602, 1558, 3799, 1669, 1162, 2737, 744, 1010]

private theorem wordMatrix109_product : wordMatrix109 = wordMatrix021 * wordMatrix073 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix109_expansion : wordMatrix109 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix109_product, wordMatrix021_expansion, wordMatrix073_expansion, mul_assoc]

def wordMatrix110 : QuotientMatrix := quotientDecode #v[2547, 2566, 3592, 249, 3344, 472, 3859, 1164, 1986, 3177, 2208, 3653]

private theorem wordMatrix110_product : wordMatrix110 = wordMatrix073 * wordMatrix021 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix110_expansion : wordMatrix110 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix110_product, wordMatrix073_expansion, wordMatrix021_expansion, mul_assoc]

def wordMatrix111 : QuotientMatrix := quotientDecode #v[1362, 3454, 1740, 1104, 1173, 3543, 510, 1982, 1747, 923, 1751, 1786]

private theorem wordMatrix111_product : wordMatrix111 = wordMatrix109 * wordMatrix110 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix111_expansion : wordMatrix111 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix111_product, wordMatrix109_expansion, wordMatrix110_expansion, mul_assoc]

def wordMatrix112 : QuotientMatrix := quotientDecode #v[3668, 3068, 3934, 669, 1286, 3867, 302, 2359, 2404, 4014, 3542, 2319]

private theorem wordMatrix112_product : wordMatrix112 = wordMatrix027 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix112_expansion : wordMatrix112 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))) := by
  simp only [wordMatrix112_product, wordMatrix027_expansion, mul_assoc]

def wordMatrix113 : QuotientMatrix := quotientDecode #v[2918, 177, 1954, 2558, 237, 2644, 3423, 3593, 2767, 3534, 1425, 2333]

private theorem wordMatrix113_product : wordMatrix113 = wordMatrix111 * wordMatrix112 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix113_expansion : wordMatrix113 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix113_product, wordMatrix111_expansion, wordMatrix112_expansion, mul_assoc]

def wordMatrix114 : QuotientMatrix := quotientDecode #v[3267, 748, 1985, 3872, 1765, 2554, 966, 915, 2969, 2683, 1216, 2830]

private theorem wordMatrix114_product : wordMatrix114 = wordMatrix009 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix114_expansion : wordMatrix114 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix114_product, wordMatrix009_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix115 : QuotientMatrix := quotientDecode #v[3120, 1835, 629, 3040, 1751, 3333, 742, 2821, 1636, 272, 3992, 634]

private theorem wordMatrix115_product : wordMatrix115 = wordMatrix066 * wordMatrix036 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix115_expansion : wordMatrix115 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix115_product, wordMatrix066_expansion, wordMatrix036_expansion, mul_assoc]

def wordMatrix116 : QuotientMatrix := quotientDecode #v[3866, 3171, 3391, 1939, 1067, 2788, 3017, 445, 3852, 2725, 1659, 2992]

private theorem wordMatrix116_product : wordMatrix116 = wordMatrix114 * wordMatrix115 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix116_expansion : wordMatrix116 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix116_product, wordMatrix114_expansion, wordMatrix115_expansion, mul_assoc]

def wordMatrix117 : QuotientMatrix := quotientDecode #v[3238, 3326, 2814, 3247, 1311, 1909, 780, 1582, 1636, 2816, 3992, 2326]

private theorem wordMatrix117_product : wordMatrix117 = wordMatrix008 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix117_expansion : wordMatrix117 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY)))) := by
  simp only [wordMatrix117_product, wordMatrix008_expansion, mul_assoc]

def wordMatrix118 : QuotientMatrix := quotientDecode #v[3748, 687, 1161, 405, 1050, 2751, 345, 2263, 3515, 1301, 2313, 54]

private theorem wordMatrix118_product : wordMatrix118 = wordMatrix116 * wordMatrix117 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix118_expansion : wordMatrix118 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix118_product, wordMatrix116_expansion, wordMatrix117_expansion, mul_assoc]

def wordMatrix119 : QuotientMatrix := quotientDecode #v[2763, 2765, 2313, 3776, 2511, 3809, 1460, 187, 3349, 2296, 4060, 3010]

private theorem wordMatrix119_product : wordMatrix119 = wordMatrix096 * wordMatrix101 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix119_expansion : wordMatrix119 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix119_product, wordMatrix096_expansion, wordMatrix101_expansion, mul_assoc]

def wordMatrix120 : QuotientMatrix := quotientDecode #v[3523, 1695, 3371, 3733, 3627, 3279, 2427, 3308, 3943, 218, 4013, 4042]

private theorem wordMatrix120_product : wordMatrix120 = wordMatrix019 * wordMatrix101 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix120_expansion : wordMatrix120 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix120_product, wordMatrix019_expansion, wordMatrix101_expansion, mul_assoc]

def wordMatrix121 : QuotientMatrix := quotientDecode #v[3918, 1274, 1019, 1322, 3544, 1062, 1001, 3009, 451, 1580, 2008, 895]

private theorem wordMatrix121_product : wordMatrix121 = wordMatrix119 * wordMatrix120 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix121_expansion : wordMatrix121 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix121_product, wordMatrix119_expansion, wordMatrix120_expansion, mul_assoc]

def wordMatrix122 : QuotientMatrix := quotientDecode #v[3206, 2829, 1677, 1450, 1422, 1685, 455, 3334, 3463, 2584, 2235, 2108]

private theorem wordMatrix122_product : wordMatrix122 = wordMatrix076 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix122_expansion : wordMatrix122 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))) := by
  simp only [wordMatrix122_product, wordMatrix076_expansion, mul_assoc]

def wordMatrix123 : QuotientMatrix := quotientDecode #v[3829, 2502, 2660, 3342, 485, 942, 1255, 4068, 1741, 1809, 961, 495]

private theorem wordMatrix123_product : wordMatrix123 = wordMatrix121 * wordMatrix122 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix123_expansion : wordMatrix123 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix123_product, wordMatrix121_expansion, wordMatrix122_expansion, mul_assoc]

def wordMatrix124 : QuotientMatrix := quotientDecode #v[2596, 3673, 2709, 3112, 3963, 800, 1891, 1928, 3079, 186, 3744, 2256]

private theorem wordMatrix124_product : wordMatrix124 = wordMatrix052 * wordMatrix068 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix124_expansion : wordMatrix124 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix124_product, wordMatrix052_expansion, wordMatrix068_expansion, mul_assoc]

def wordMatrix125 : QuotientMatrix := quotientDecode #v[469, 2921, 4081, 476, 2794, 1474, 2869, 2370, 2591, 1138, 1140, 3181]

private theorem wordMatrix125_product : wordMatrix125 = wordMatrix002 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix125_expansion : wordMatrix125 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))) := by
  simp only [wordMatrix125_product, wordMatrix002_expansion, mul_assoc]

def wordMatrix126 : QuotientMatrix := quotientDecode #v[2056, 2769, 2400, 1630, 423, 1338, 805, 2034, 2110, 941, 2233, 1711]

private theorem wordMatrix126_product : wordMatrix126 = wordMatrix038 * wordMatrix125 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix126_expansion : wordMatrix126 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))) := by
  simp only [wordMatrix126_product, wordMatrix038_expansion, wordMatrix125_expansion, mul_assoc]

def wordMatrix127 : QuotientMatrix := quotientDecode #v[2392, 367, 575, 3442, 1722, 3753, 2028, 646, 1455, 4064, 3955, 991]

private theorem wordMatrix127_product : wordMatrix127 = wordMatrix124 * wordMatrix126 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix127_expansion : wordMatrix127 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))) := by
  simp only [wordMatrix127_product, wordMatrix124_expansion, wordMatrix126_expansion, mul_assoc]

def wordMatrix128 : QuotientMatrix := quotientDecode #v[3581, 3782, 3391, 451, 1182, 1685, 1399, 488, 2516, 724, 2136, 1942]

private theorem wordMatrix128_product : wordMatrix128 = wordMatrix018 * wordMatrix018 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix128_expansion : wordMatrix128 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))) := by
  simp only [wordMatrix128_product, wordMatrix018_expansion, mul_assoc]

def wordMatrix129 : QuotientMatrix := quotientDecode #v[971, 797, 2774, 2041, 3397, 800, 1401, 2280, 2718, 2096, 2116, 2997]

private theorem wordMatrix129_product : wordMatrix129 = wordMatrix128 * wordMatrix085 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix129_expansion : wordMatrix129 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix129_product, wordMatrix128_expansion, wordMatrix085_expansion, mul_assoc]

def wordMatrix130 : QuotientMatrix := quotientDecode #v[2838, 2638, 1511, 453, 33, 623, 3084, 2880, 613, 2701, 629, 3706]

private theorem wordMatrix130_product : wordMatrix130 = wordMatrix076 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix130_expansion : wordMatrix130 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix130_product, wordMatrix076_expansion, mul_assoc]

def wordMatrix131 : QuotientMatrix := quotientDecode #v[3897, 2045, 3123, 1356, 3223, 2695, 1153, 2716, 506, 3124, 1937, 365]

private theorem wordMatrix131_product : wordMatrix131 = wordMatrix129 * wordMatrix130 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix131_expansion : wordMatrix131 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix131_product, wordMatrix129_expansion, wordMatrix130_expansion, mul_assoc]

def wordMatrix132 : QuotientMatrix := quotientDecode #v[291, 3761, 3691, 3428, 1432, 1142, 2710, 2137, 2987, 2996, 3485, 780]

private theorem wordMatrix132_product : wordMatrix132 = wordMatrix077 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix132_expansion : wordMatrix132 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))) := by
  simp only [wordMatrix132_product, wordMatrix077_expansion, mul_assoc]

def wordMatrix133 : QuotientMatrix := quotientDecode #v[807, 3215, 237, 4015, 681, 280, 1255, 1654, 2911, 276, 352, 1895]

private theorem wordMatrix133_product : wordMatrix133 = wordMatrix131 * wordMatrix132 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix133_expansion : wordMatrix133 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix133_product, wordMatrix131_expansion, wordMatrix132_expansion, mul_assoc]

def wordMatrix134 : QuotientMatrix := quotientDecode #v[3446, 2445, 2715, 4036, 706, 855, 1509, 802, 1017, 3574, 2677, 3204]

private theorem wordMatrix134_product : wordMatrix134 = wordMatrix045 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix134_expansion : wordMatrix134 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix134_product, wordMatrix045_expansion, wordMatrix009_expansion, mul_assoc]

def wordMatrix135 : QuotientMatrix := quotientDecode #v[3326, 1240, 934, 3671, 3849, 3517, 223, 947, 996, 1400, 1653, 1853]

private theorem wordMatrix135_product : wordMatrix135 = wordMatrix038 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix135_expansion : wordMatrix135 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix135_product, wordMatrix038_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix136 : QuotientMatrix := quotientDecode #v[1977, 1637, 2190, 1822, 716, 714, 1048, 4089, 1517, 1034, 3958, 349]

private theorem wordMatrix136_product : wordMatrix136 = wordMatrix134 * wordMatrix135 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix136_expansion : wordMatrix136 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix136_product, wordMatrix134_expansion, wordMatrix135_expansion, mul_assoc]

def wordMatrix137 : QuotientMatrix := quotientDecode #v[1713, 1721, 1431, 3404, 2163, 3699, 1576, 3243, 348, 4041, 3212, 2688]

private theorem wordMatrix137_product : wordMatrix137 = wordMatrix136 * wordMatrix117 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix137_expansion : wordMatrix137 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix137_product, wordMatrix136_expansion, wordMatrix117_expansion, mul_assoc]

def wordMatrix138 : QuotientMatrix := quotientDecode #v[755, 1898, 2464, 453, 2780, 3649, 3181, 1498, 1524, 222, 2676, 604]

private theorem wordMatrix138_product : wordMatrix138 = wordMatrix030 * wordMatrix057 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix138_expansion : wordMatrix138 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix138_product, wordMatrix030_expansion, wordMatrix057_expansion, mul_assoc]

def wordMatrix139 : QuotientMatrix := quotientDecode #v[99, 2604, 282, 3428, 1200, 2095, 14, 2457, 607, 120, 9, 132]

private theorem wordMatrix139_product : wordMatrix139 = wordMatrix057 * wordMatrix038 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix139_expansion : wordMatrix139 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix139_product, wordMatrix057_expansion, wordMatrix038_expansion, mul_assoc]

def wordMatrix140 : QuotientMatrix := quotientDecode #v[3903, 3399, 877, 2737, 421, 152, 1201, 2105, 1604, 2933, 3447, 2232]

private theorem wordMatrix140_product : wordMatrix140 = wordMatrix138 * wordMatrix139 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix140_expansion : wordMatrix140 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix140_product, wordMatrix138_expansion, wordMatrix139_expansion, mul_assoc]

def wordMatrix141 : QuotientMatrix := quotientDecode #v[2070, 817, 3544, 2737, 2835, 91, 3780, 655, 1249, 3539, 352, 2962]

private theorem wordMatrix141_product : wordMatrix141 = wordMatrix140 * wordMatrix048 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix141_expansion : wordMatrix141 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix141_product, wordMatrix140_expansion, wordMatrix048_expansion, mul_assoc]

def wordMatrix142 : QuotientMatrix := quotientDecode #v[165, 2081, 3424, 746, 1395, 3555, 2649, 2098, 3163, 3302, 2446, 3238]

private theorem wordMatrix142_product : wordMatrix142 = wordMatrix027 * wordMatrix074 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix142_expansion : wordMatrix142 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix142_product, wordMatrix027_expansion, wordMatrix074_expansion, mul_assoc]

def wordMatrix143 : QuotientMatrix := quotientDecode #v[2211, 2262, 2590, 2351, 2717, 605, 1456, 796, 4083, 1242, 1125, 1926]

private theorem wordMatrix143_product : wordMatrix143 = wordMatrix021 * wordMatrix024 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix143_expansion : wordMatrix143 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix143_product, wordMatrix021_expansion, wordMatrix024_expansion, mul_assoc]

def wordMatrix144 : QuotientMatrix := quotientDecode #v[1020, 3448, 3069, 466, 1683, 2196, 3581, 1936, 1428, 1498, 142, 106]

private theorem wordMatrix144_product : wordMatrix144 = wordMatrix142 * wordMatrix143 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix144_expansion : wordMatrix144 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix144_product, wordMatrix142_expansion, wordMatrix143_expansion, mul_assoc]

def wordMatrix145 : QuotientMatrix := quotientDecode #v[1088, 829, 3134, 1113, 1772, 2528, 611, 2224, 2092, 3871, 695, 1082]

private theorem wordMatrix145_product : wordMatrix145 = wordMatrix016 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix145_expansion : wordMatrix145 = matrixX * (matrixYInv * (matrixX)) := by
  simp only [wordMatrix145_product, wordMatrix016_expansion, mul_assoc]

def wordMatrix146 : QuotientMatrix := quotientDecode #v[2699, 1943, 2801, 1838, 1161, 1624, 1881, 3032, 2297, 448, 1002, 3303]

private theorem wordMatrix146_product : wordMatrix146 = wordMatrix144 * wordMatrix145 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix146_expansion : wordMatrix146 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix146_product, wordMatrix144_expansion, wordMatrix145_expansion, mul_assoc]

def wordMatrix147 : QuotientMatrix := quotientDecode #v[1691, 468, 2125, 3986, 730, 3450, 236, 823, 693, 260, 282, 3652]

private theorem wordMatrix147_product : wordMatrix147 = wordMatrix006 * wordMatrix003 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix147_expansion : wordMatrix147 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))) := by
  simp only [wordMatrix147_product, wordMatrix006_expansion, wordMatrix003_expansion, mul_assoc]

def wordMatrix148 : QuotientMatrix := quotientDecode #v[725, 907, 2924, 3786, 3860, 1800, 1315, 3295, 3428, 3708, 233, 3362]

private theorem wordMatrix148_product : wordMatrix148 = wordMatrix147 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix148_expansion : wordMatrix148 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix148_product, wordMatrix147_expansion, wordMatrix009_expansion, mul_assoc]

def wordMatrix149 : QuotientMatrix := quotientDecode #v[3933, 2704, 779, 1604, 3938, 1062, 479, 1451, 2681, 26, 3939, 138]

private theorem wordMatrix149_product : wordMatrix149 = wordMatrix004 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix149_expansion : wordMatrix149 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix149_product, wordMatrix004_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix150 : QuotientMatrix := quotientDecode #v[1882, 3137, 2655, 1875, 2531, 836, 1265, 1149, 866, 39, 2379, 2854]

private theorem wordMatrix150_product : wordMatrix150 = wordMatrix148 * wordMatrix149 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix150_expansion : wordMatrix150 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix150_product, wordMatrix148_expansion, wordMatrix149_expansion, mul_assoc]

def wordMatrix151 : QuotientMatrix := quotientDecode #v[1872, 3555, 1551, 2147, 4056, 2791, 3979, 2747, 1737, 2933, 142, 553]

private theorem wordMatrix151_product : wordMatrix151 = wordMatrix150 * wordMatrix000 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix151_expansion : wordMatrix151 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix151_product, wordMatrix150_expansion, wordMatrix000_expansion, mul_assoc]

def wordMatrix152 : QuotientMatrix := quotientDecode #v[2389, 3446, 3542, 1228, 1139, 2174, 3971, 2239, 721, 2658, 2212, 3905]

private theorem wordMatrix152_product : wordMatrix152 = wordMatrix052 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix152_expansion : wordMatrix152 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix152_product, wordMatrix052_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix153 : QuotientMatrix := quotientDecode #v[3387, 3778, 41, 3403, 2988, 1090, 815, 1403, 3353, 3642, 2642, 1198]

private theorem wordMatrix153_product : wordMatrix153 = wordMatrix050 * wordMatrix052 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix153_expansion : wordMatrix153 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix153_product, wordMatrix050_expansion, wordMatrix052_expansion, mul_assoc]

def wordMatrix154 : QuotientMatrix := quotientDecode #v[3110, 463, 246, 356, 1386, 3023, 2909, 160, 3833, 827, 1470, 971]

private theorem wordMatrix154_product : wordMatrix154 = wordMatrix152 * wordMatrix153 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix154_expansion : wordMatrix154 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix154_product, wordMatrix152_expansion, wordMatrix153_expansion, mul_assoc]

def wordMatrix155 : QuotientMatrix := quotientDecode #v[3277, 3705, 1867, 486, 3419, 2754, 1881, 1968, 3309, 508, 1314, 1763]

private theorem wordMatrix155_product : wordMatrix155 = wordMatrix154 * wordMatrix064 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix155_expansion : wordMatrix155 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix155_product, wordMatrix154_expansion, wordMatrix064_expansion, mul_assoc]

def wordMatrix156 : QuotientMatrix := quotientDecode #v[2211, 3107, 2130, 2094, 112, 4063, 2269, 1569, 3247, 3307, 2677, 1123]

private theorem wordMatrix156_product : wordMatrix156 = wordMatrix147 * wordMatrix057 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix156_expansion : wordMatrix156 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix156_product, wordMatrix147_expansion, wordMatrix057_expansion, mul_assoc]

def wordMatrix157 : QuotientMatrix := quotientDecode #v[1475, 2430, 1563, 3099, 934, 531, 3230, 1369, 1447, 2193, 893, 842]

private theorem wordMatrix157_product : wordMatrix157 = wordMatrix001 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix157_expansion : wordMatrix157 = matrixY * (matrixX * (matrixY)) := by
  simp only [wordMatrix157_product, wordMatrix001_expansion, mul_assoc]

def wordMatrix158 : QuotientMatrix := quotientDecode #v[1313, 2753, 670, 1461, 3371, 1614, 1697, 4005, 1802, 675, 40, 2195]

private theorem wordMatrix158_product : wordMatrix158 = wordMatrix003 * wordMatrix157 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix158_expansion : wordMatrix158 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))) := by
  simp only [wordMatrix158_product, wordMatrix003_expansion, wordMatrix157_expansion, mul_assoc]

def wordMatrix159 : QuotientMatrix := quotientDecode #v[1327, 3695, 856, 1774, 3864, 1012, 1184, 428, 1471, 3345, 2623, 3756]

private theorem wordMatrix159_product : wordMatrix159 = wordMatrix030 * wordMatrix158 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix159_expansion : wordMatrix159 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))) := by
  simp only [wordMatrix159_product, wordMatrix030_expansion, wordMatrix158_expansion, mul_assoc]

def wordMatrix160 : QuotientMatrix := quotientDecode #v[1972, 3111, 2939, 1665, 2124, 2271, 1057, 501, 2109, 4037, 3462, 1579]

private theorem wordMatrix160_product : wordMatrix160 = wordMatrix156 * wordMatrix159 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix160_expansion : wordMatrix160 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))) := by
  simp only [wordMatrix160_product, wordMatrix156_expansion, wordMatrix159_expansion, mul_assoc]

def wordMatrix161 : QuotientMatrix := quotientDecode #v[1687, 3859, 3759, 3707, 3002, 1021, 2854, 2277, 191, 2084, 1765, 3150]

private theorem wordMatrix161_product : wordMatrix161 = wordMatrix128 * wordMatrix101 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix161_expansion : wordMatrix161 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix161_product, wordMatrix128_expansion, wordMatrix101_expansion, mul_assoc]

def wordMatrix162 : QuotientMatrix := quotientDecode #v[2883, 1585, 2374, 2986, 606, 3021, 1776, 278, 1782, 2756, 854, 1132]

private theorem wordMatrix162_product : wordMatrix162 = wordMatrix074 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix162_expansion : wordMatrix162 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix162_product, wordMatrix074_expansion, wordMatrix019_expansion, mul_assoc]

def wordMatrix163 : QuotientMatrix := quotientDecode #v[3822, 1060, 2235, 1093, 3392, 3048, 3300, 2626, 1819, 1767, 1980, 1303]

private theorem wordMatrix163_product : wordMatrix163 = wordMatrix161 * wordMatrix162 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix163_expansion : wordMatrix163 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix163_product, wordMatrix161_expansion, wordMatrix162_expansion, mul_assoc]

def wordMatrix164 : QuotientMatrix := quotientDecode #v[1201, 3475, 4025, 2324, 4091, 2146, 1881, 1854, 1055, 182, 3536, 1763]

private theorem wordMatrix164_product : wordMatrix164 = wordMatrix163 * wordMatrix027 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix164_expansion : wordMatrix164 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix164_product, wordMatrix163_expansion, wordMatrix027_expansion, mul_assoc]

def wordMatrix165 : QuotientMatrix := quotientDecode #v[60, 807, 4007, 1741, 660, 1046, 3455, 467, 3353, 1185, 1815, 3426]

private theorem wordMatrix165_product : wordMatrix165 = wordMatrix021 * wordMatrix101 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix165_expansion : wordMatrix165 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix165_product, wordMatrix021_expansion, wordMatrix101_expansion, mul_assoc]

def wordMatrix166 : QuotientMatrix := quotientDecode #v[2736, 3220, 1121, 1825, 3651, 3477, 991, 1322, 3815, 1622, 3947, 862]

private theorem wordMatrix166_product : wordMatrix166 = wordMatrix101 * wordMatrix027 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix166_expansion : wordMatrix166 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix166_product, wordMatrix101_expansion, wordMatrix027_expansion, mul_assoc]

def wordMatrix167 : QuotientMatrix := quotientDecode #v[150, 1889, 3710, 1592, 2398, 2525, 1983, 117, 256, 3428, 3036, 12]

private theorem wordMatrix167_product : wordMatrix167 = wordMatrix165 * wordMatrix166 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix167_expansion : wordMatrix167 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix167_product, wordMatrix165_expansion, wordMatrix166_expansion, mul_assoc]

def wordMatrix168 : QuotientMatrix := quotientDecode #v[4067, 832, 764, 1437, 2616, 3385, 2721, 1958, 2905, 2074, 1755, 1965]

private theorem wordMatrix168_product : wordMatrix168 = wordMatrix020 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix168_expansion : wordMatrix168 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))) := by
  simp only [wordMatrix168_product, wordMatrix020_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix169 : QuotientMatrix := quotientDecode #v[3106, 3555, 237, 3165, 2124, 841, 3837, 191, 2905, 3915, 1200, 1889]

private theorem wordMatrix169_product : wordMatrix169 = wordMatrix167 * wordMatrix168 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix169_expansion : wordMatrix169 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix169_product, wordMatrix167_expansion, wordMatrix168_expansion, mul_assoc]

def wordMatrix170 : QuotientMatrix := quotientDecode #v[1833, 2753, 934, 3619, 1213, 1234, 1540, 3168, 669, 617, 25, 2598]

private theorem wordMatrix170_product : wordMatrix170 = wordMatrix050 * wordMatrix038 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix170_expansion : wordMatrix170 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix170_product, wordMatrix050_expansion, wordMatrix038_expansion, mul_assoc]

def wordMatrix171 : QuotientMatrix := quotientDecode #v[3887, 611, 2746, 298, 2484, 2894, 1462, 1664, 387, 1536, 831, 1855]

private theorem wordMatrix171_product : wordMatrix171 = wordMatrix012 * wordMatrix068 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix171_expansion : wordMatrix171 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix171_product, wordMatrix012_expansion, wordMatrix068_expansion, mul_assoc]

def wordMatrix172 : QuotientMatrix := quotientDecode #v[503, 3366, 660, 1026, 1018, 3038, 3973, 2808, 3467, 1789, 1969, 680]

private theorem wordMatrix172_product : wordMatrix172 = wordMatrix170 * wordMatrix171 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix172_expansion : wordMatrix172 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix172_product, wordMatrix170_expansion, wordMatrix171_expansion, mul_assoc]

def wordMatrix173 : QuotientMatrix := quotientDecode #v[1907, 2278, 2165, 2563, 33, 1891, 2944, 4018, 111, 3165, 3940, 960]

private theorem wordMatrix173_product : wordMatrix173 = wordMatrix172 * wordMatrix157 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix173_expansion : wordMatrix173 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix173_product, wordMatrix172_expansion, wordMatrix157_expansion, mul_assoc]

def wordMatrix174 : QuotientMatrix := quotientDecode #v[3887, 1726, 2966, 2451, 2590, 4072, 689, 3016, 3911, 2633, 2774, 2432]

private theorem wordMatrix174_product : wordMatrix174 = wordMatrix074 * wordMatrix073 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix174_expansion : wordMatrix174 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix174_product, wordMatrix074_expansion, wordMatrix073_expansion, mul_assoc]

def wordMatrix175 : QuotientMatrix := quotientDecode #v[2349, 1453, 9, 1301, 1941, 424, 1362, 2643, 1005, 2119, 1239, 1456]

private theorem wordMatrix175_product : wordMatrix175 = wordMatrix073 * wordMatrix077 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix175_expansion : wordMatrix175 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix175_product, wordMatrix073_expansion, wordMatrix077_expansion, mul_assoc]

def wordMatrix176 : QuotientMatrix := quotientDecode #v[761, 79, 1656, 1819, 2771, 369, 3332, 1038, 790, 1181, 199, 3086]

private theorem wordMatrix176_product : wordMatrix176 = wordMatrix174 * wordMatrix175 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix176_expansion : wordMatrix176 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix176_product, wordMatrix174_expansion, wordMatrix175_expansion, mul_assoc]

def wordMatrix177 : QuotientMatrix := quotientDecode #v[535, 3324, 158, 3428, 2484, 134, 2395, 945, 3746, 2297, 2213, 2729]

private theorem wordMatrix177_product : wordMatrix177 = wordMatrix176 * wordMatrix018 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix177_expansion : wordMatrix177 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix177_product, wordMatrix176_expansion, wordMatrix018_expansion, mul_assoc]

def wordMatrix178 : QuotientMatrix := quotientDecode #v[908, 2278, 3041, 2143, 631, 555, 1675, 661, 1866, 3881, 1161, 1734]

private theorem wordMatrix178_product : wordMatrix178 = wordMatrix004 * wordMatrix147 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix178_expansion : wordMatrix178 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix178_product, wordMatrix004_expansion, wordMatrix147_expansion, mul_assoc]

def wordMatrix179 : QuotientMatrix := quotientDecode #v[1327, 2832, 3759, 3428, 3392, 3478, 4042, 1741, 3383, 2240, 1200, 3504]

private theorem wordMatrix179_product : wordMatrix179 = wordMatrix066 * wordMatrix007 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix179_expansion : wordMatrix179 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix179_product, wordMatrix066_expansion, wordMatrix007_expansion, mul_assoc]

def wordMatrix180 : QuotientMatrix := quotientDecode #v[241, 3230, 2553, 718, 1868, 1549, 2534, 2253, 2297, 2346, 2614, 200]

private theorem wordMatrix180_product : wordMatrix180 = wordMatrix178 * wordMatrix179 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix180_expansion : wordMatrix180 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix180_product, wordMatrix178_expansion, wordMatrix179_expansion, mul_assoc]

def wordMatrix181 : QuotientMatrix := quotientDecode #v[1465, 3225, 1121, 108, 2772, 1319, 2944, 26, 967, 727, 1291, 2267]

private theorem wordMatrix181_product : wordMatrix181 = wordMatrix180 * wordMatrix048 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix181_expansion : wordMatrix181 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix181_product, wordMatrix180_expansion, wordMatrix048_expansion, mul_assoc]

def wordMatrix182 : QuotientMatrix := quotientDecode #v[3732, 749, 2025, 381, 135, 439, 1443, 450, 1176, 3463, 3348, 3973]

private theorem wordMatrix182_product : wordMatrix182 = wordMatrix038 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix182_expansion : wordMatrix182 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix182_product, wordMatrix038_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix183 : QuotientMatrix := quotientDecode #v[1584, 3618, 3938, 2756, 3860, 2703, 3543, 2981, 3796, 2391, 2814, 583]

private theorem wordMatrix183_product : wordMatrix183 = wordMatrix147 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix183_expansion : wordMatrix183 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix183_product, wordMatrix147_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix184 : QuotientMatrix := quotientDecode #v[2621, 1596, 3444, 1294, 3285, 1946, 3346, 1668, 1163, 2744, 1563, 3533]

private theorem wordMatrix184_product : wordMatrix184 = wordMatrix182 * wordMatrix183 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix184_expansion : wordMatrix184 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix184_product, wordMatrix182_expansion, wordMatrix183_expansion, mul_assoc]

def wordMatrix185 : QuotientMatrix := quotientDecode #v[1800, 1971, 4076, 2107, 2242, 3166, 1205, 2880, 782, 1421, 670, 498]

private theorem wordMatrix185_product : wordMatrix185 = wordMatrix184 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix185_expansion : wordMatrix185 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix185_product, wordMatrix184_expansion, mul_assoc]

def wordMatrix186 : QuotientMatrix := quotientDecode #v[369, 3563, 1501, 551, 3027, 1393, 3668, 2748, 287, 1301, 1678, 475]

private theorem wordMatrix186_product : wordMatrix186 = wordMatrix045 * wordMatrix032 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix186_expansion : wordMatrix186 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix186_product, wordMatrix045_expansion, wordMatrix032_expansion, mul_assoc]

def wordMatrix187 : QuotientMatrix := quotientDecode #v[1533, 236, 1440, 1682, 1427, 1385, 2560, 1333, 637, 3114, 3462, 150]

private theorem wordMatrix187_product : wordMatrix187 = wordMatrix012 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix187_expansion : wordMatrix187 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix187_product, wordMatrix012_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix188 : QuotientMatrix := quotientDecode #v[3450, 1714, 914, 2546, 374, 252, 2825, 2625, 461, 2613, 1863, 2904]

private theorem wordMatrix188_product : wordMatrix188 = wordMatrix186 * wordMatrix187 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix188_expansion : wordMatrix188 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix188_product, wordMatrix186_expansion, wordMatrix187_expansion, mul_assoc]

def wordMatrix189 : QuotientMatrix := quotientDecode #v[3215, 1465, 1755, 92, 3143, 3268, 3866, 685, 1729, 3428, 732, 3093]

private theorem wordMatrix189_product : wordMatrix189 = wordMatrix188 * wordMatrix064 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix189_expansion : wordMatrix189 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix189_product, wordMatrix188_expansion, wordMatrix064_expansion, mul_assoc]

def wordMatrix190 : QuotientMatrix := quotientDecode #v[3220, 2396, 3143, 909, 3940, 1734, 2672, 2280, 1604, 3510, 1182, 785]

private theorem wordMatrix190_product : wordMatrix190 = wordMatrix076 * wordMatrix084 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix190_expansion : wordMatrix190 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix190_product, wordMatrix076_expansion, wordMatrix084_expansion, mul_assoc]

def wordMatrix191 : QuotientMatrix := quotientDecode #v[1159, 2259, 2322, 2540, 2185, 3559, 2248, 2012, 1669, 728, 1306, 846]

private theorem wordMatrix191_product : wordMatrix191 = wordMatrix019 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix191_expansion : wordMatrix191 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix191_product, wordMatrix019_expansion, mul_assoc]

def wordMatrix192 : QuotientMatrix := quotientDecode #v[19, 1396, 3034, 2040, 3636, 2327, 3120, 2129, 1560, 930, 610, 2131]

private theorem wordMatrix192_product : wordMatrix192 = wordMatrix190 * wordMatrix191 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix192_expansion : wordMatrix192 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix192_product, wordMatrix190_expansion, wordMatrix191_expansion, mul_assoc]

def wordMatrix193 : QuotientMatrix := quotientDecode #v[3809, 2894, 2833, 1403, 1543, 1308, 1372, 2096, 1152, 2514, 679, 3062]

private theorem wordMatrix193_product : wordMatrix193 = wordMatrix023 * wordMatrix081 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix193_expansion : wordMatrix193 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))) := by
  simp only [wordMatrix193_product, wordMatrix023_expansion, wordMatrix081_expansion, mul_assoc]

def wordMatrix194 : QuotientMatrix := quotientDecode #v[936, 2929, 1018, 1273, 2185, 1999, 2634, 1612, 2057, 2864, 732, 3330]

private theorem wordMatrix194_product : wordMatrix194 = wordMatrix192 * wordMatrix193 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix194_expansion : wordMatrix194 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix194_product, wordMatrix192_expansion, wordMatrix193_expansion, mul_assoc]

def wordMatrix195 : QuotientMatrix := quotientDecode #v[3449, 756, 636, 3770, 41, 3795, 1901, 438, 2945, 3489, 282, 2409]

private theorem wordMatrix195_product : wordMatrix195 = wordMatrix101 * wordMatrix084 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix195_expansion : wordMatrix195 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix195_product, wordMatrix101_expansion, wordMatrix084_expansion, mul_assoc]

def wordMatrix196 : QuotientMatrix := quotientDecode #v[1760, 3101, 1674, 304, 1067, 3628, 1153, 2821, 3345, 3944, 4013, 3107]

private theorem wordMatrix196_product : wordMatrix196 = wordMatrix084 * wordMatrix101 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix196_expansion : wordMatrix196 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix196_product, wordMatrix084_expansion, wordMatrix101_expansion, mul_assoc]

def wordMatrix197 : QuotientMatrix := quotientDecode #v[1993, 3169, 1620, 201, 2556, 3508, 1571, 1668, 959, 3414, 1047, 3151]

private theorem wordMatrix197_product : wordMatrix197 = wordMatrix195 * wordMatrix196 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix197_expansion : wordMatrix197 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix197_product, wordMatrix195_expansion, wordMatrix196_expansion, mul_assoc]

def wordMatrix198 : QuotientMatrix := quotientDecode #v[545, 3588, 664, 221, 1788, 3787, 343, 616, 2711, 1259, 105, 2001]

private theorem wordMatrix198_product : wordMatrix198 = wordMatrix018 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix198_expansion : wordMatrix198 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))) := by
  simp only [wordMatrix198_product, wordMatrix018_expansion, mul_assoc]

def wordMatrix199 : QuotientMatrix := quotientDecode #v[4054, 2565, 433, 451, 1035, 1512, 1644, 1138, 2627, 1560, 2088, 2191]

private theorem wordMatrix199_product : wordMatrix199 = wordMatrix197 * wordMatrix198 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix199_expansion : wordMatrix199 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix199_product, wordMatrix197_expansion, wordMatrix198_expansion, mul_assoc]

def wordMatrix200 : QuotientMatrix := quotientDecode #v[957, 3562, 1903, 2521, 1295, 689, 2766, 2486, 1451, 72, 1492, 1759]

private theorem wordMatrix200_product : wordMatrix200 = wordMatrix024 * wordMatrix084 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix200_expansion : wordMatrix200 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix200_product, wordMatrix024_expansion, wordMatrix084_expansion, mul_assoc]

def wordMatrix201 : QuotientMatrix := quotientDecode #v[3803, 793, 575, 2629, 2852, 971, 3801, 3099, 387, 1168, 289, 3892]

private theorem wordMatrix201_product : wordMatrix201 = wordMatrix080 * wordMatrix085 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix201_expansion : wordMatrix201 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix201_product, wordMatrix080_expansion, wordMatrix085_expansion, mul_assoc]

def wordMatrix202 : QuotientMatrix := quotientDecode #v[1862, 1987, 3224, 975, 1306, 3775, 517, 2917, 2293, 1180, 2939, 2543]

private theorem wordMatrix202_product : wordMatrix202 = wordMatrix200 * wordMatrix201 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix202_expansion : wordMatrix202 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix202_product, wordMatrix200_expansion, wordMatrix201_expansion, mul_assoc]

def wordMatrix203 : QuotientMatrix := quotientDecode #v[1247, 379, 1976, 1356, 629, 1730, 2910, 1564, 2153, 2298, 2113, 3846]

private theorem wordMatrix203_product : wordMatrix203 = wordMatrix202 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix203_expansion : wordMatrix203 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix203_product, wordMatrix202_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix204 : QuotientMatrix := quotientDecode #v[1987, 509, 1103, 136, 4046, 611, 3275, 693, 3638, 204, 1969, 1855]

private theorem wordMatrix204_product : wordMatrix204 = wordMatrix174 * wordMatrix075 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix204_expansion : wordMatrix204 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix204_product, wordMatrix174_expansion, wordMatrix075_expansion, mul_assoc]

def wordMatrix205 : QuotientMatrix := quotientDecode #v[490, 543, 1511, 646, 2930, 3205, 2647, 2599, 1469, 3178, 1191, 968]

private theorem wordMatrix205_product : wordMatrix205 = wordMatrix080 * wordMatrix016 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix205_expansion : wordMatrix205 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))) := by
  simp only [wordMatrix205_product, wordMatrix080_expansion, wordMatrix016_expansion, mul_assoc]

def wordMatrix206 : QuotientMatrix := quotientDecode #v[3829, 1201, 2660, 2209, 2998, 2381, 1644, 1463, 2826, 1809, 330, 3603]

private theorem wordMatrix206_product : wordMatrix206 = wordMatrix204 * wordMatrix205 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix206_expansion : wordMatrix206 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix206_product, wordMatrix204_expansion, wordMatrix205_expansion, mul_assoc]

def wordMatrix207 : QuotientMatrix := quotientDecode #v[4011, 3831, 1051, 3878, 575, 157, 56, 3872, 2030, 2467, 2622, 4038]

private theorem wordMatrix207_product : wordMatrix207 = wordMatrix004 * wordMatrix052 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix207_expansion : wordMatrix207 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix207_product, wordMatrix004_expansion, wordMatrix052_expansion, mul_assoc]

def wordMatrix208 : QuotientMatrix := quotientDecode #v[3364, 2938, 55, 1982, 1511, 79, 168, 3095, 1138, 1006, 2636, 3825]

private theorem wordMatrix208_product : wordMatrix208 = wordMatrix149 * wordMatrix207 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix208_expansion : wordMatrix208 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix208_product, wordMatrix149_expansion, wordMatrix207_expansion, mul_assoc]

def wordMatrix209 : QuotientMatrix := quotientDecode #v[3788, 3096, 4, 4089, 2374, 1274, 755, 1442, 1455, 1928, 2780, 2364]

private theorem wordMatrix209_product : wordMatrix209 = wordMatrix208 * wordMatrix003 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix209_expansion : wordMatrix209 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix209_product, wordMatrix208_expansion, wordMatrix003_expansion, mul_assoc]

def wordMatrix210 : QuotientMatrix := quotientDecode #v[3709, 726, 1140, 1323, 2498, 1166, 1746, 1077, 2280, 1613, 3524, 343]

private theorem wordMatrix210_product : wordMatrix210 = wordMatrix021 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix210_expansion : wordMatrix210 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix210_product, wordMatrix021_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix211 : QuotientMatrix := quotientDecode #v[2941, 1368, 1792, 571, 1771, 3367, 1354, 513, 982, 3122, 1019, 2401]

private theorem wordMatrix211_product : wordMatrix211 = wordMatrix018 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix211_expansion : wordMatrix211 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))) := by
  simp only [wordMatrix211_product, wordMatrix018_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix212 : QuotientMatrix := quotientDecode #v[3745, 1486, 323, 3286, 1295, 3245, 510, 1962, 206, 2895, 2998, 1512]

private theorem wordMatrix212_product : wordMatrix212 = wordMatrix087 * wordMatrix211 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix212_expansion : wordMatrix212 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))) := by
  simp only [wordMatrix212_product, wordMatrix087_expansion, wordMatrix211_expansion, mul_assoc]

def wordMatrix213 : QuotientMatrix := quotientDecode #v[3705, 3225, 681, 108, 1724, 1095, 1644, 3574, 967, 563, 2439, 3603]

private theorem wordMatrix213_product : wordMatrix213 = wordMatrix210 * wordMatrix212 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix213_expansion : wordMatrix213 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))) := by
  simp only [wordMatrix213_product, wordMatrix210_expansion, wordMatrix212_expansion, mul_assoc]

def wordMatrix214 : QuotientMatrix := quotientDecode #v[1519, 60, 1074, 3870, 268, 522, 1746, 3405, 3626, 3177, 2208, 3692]

private theorem wordMatrix214_product : wordMatrix214 = wordMatrix038 * wordMatrix057 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix214_expansion : wordMatrix214 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix214_product, wordMatrix038_expansion, wordMatrix057_expansion, mul_assoc]

def wordMatrix215 : QuotientMatrix := quotientDecode #v[2912, 2458, 3972, 759, 2288, 1272, 4038, 3032, 1077, 1843, 3378, 82]

private theorem wordMatrix215_product : wordMatrix215 = wordMatrix038 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix215_expansion : wordMatrix215 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))) := by
  simp only [wordMatrix215_product, wordMatrix038_expansion, mul_assoc]

def wordMatrix216 : QuotientMatrix := quotientDecode #v[1640, 379, 2208, 639, 2374, 3166, 3957, 128, 1478, 4041, 3954, 3102]

private theorem wordMatrix216_product : wordMatrix216 = wordMatrix214 * wordMatrix215 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix216_expansion : wordMatrix216 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))) := by
  simp only [wordMatrix216_product, wordMatrix214_expansion, wordMatrix215_expansion, mul_assoc]

def wordMatrix217 : QuotientMatrix := quotientDecode #v[1963, 2973, 1182, 3079, 3391, 3267, 3257, 2888, 740, 3243, 2008, 924]

private theorem wordMatrix217_product : wordMatrix217 = wordMatrix156 * wordMatrix148 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix217_expansion : wordMatrix217 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix217_product, wordMatrix156_expansion, wordMatrix148_expansion, mul_assoc]

def wordMatrix218 : QuotientMatrix := quotientDecode #v[3577, 3664, 664, 3412, 2495, 210, 3706, 2281, 3126, 4089, 856, 1000]

private theorem wordMatrix218_product : wordMatrix218 = wordMatrix217 * wordMatrix125 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix218_expansion : wordMatrix218 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix218_product, wordMatrix217_expansion, wordMatrix125_expansion, mul_assoc]

def wordMatrix219 : QuotientMatrix := quotientDecode #v[1446, 3086, 2676, 1809, 1877, 3761, 2699, 3305, 3405, 1736, 1653, 1886]

private theorem wordMatrix219_product : wordMatrix219 = wordMatrix027 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix219_expansion : wordMatrix219 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix219_product, wordMatrix027_expansion, wordMatrix019_expansion, mul_assoc]

def wordMatrix220 : QuotientMatrix := quotientDecode #v[3135, 913, 2970, 3323, 627, 2364, 1370, 315, 394, 3647, 1066, 784]

private theorem wordMatrix220_product : wordMatrix220 = wordMatrix085 * wordMatrix073 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix220_expansion : wordMatrix220 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix220_product, wordMatrix085_expansion, wordMatrix073_expansion, mul_assoc]

def wordMatrix221 : QuotientMatrix := quotientDecode #v[1452, 970, 2208, 1491, 2835, 3918, 3905, 2723, 2228, 655, 933, 2118]

private theorem wordMatrix221_product : wordMatrix221 = wordMatrix219 * wordMatrix220 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix221_expansion : wordMatrix221 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix221_product, wordMatrix219_expansion, wordMatrix220_expansion, mul_assoc]

def wordMatrix222 : QuotientMatrix := quotientDecode #v[3773, 2797, 3271, 1560, 25, 3668, 132, 4018, 1807, 2581, 3030, 2736]

private theorem wordMatrix222_product : wordMatrix222 = wordMatrix221 * wordMatrix099 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix222_expansion : wordMatrix222 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix222_product, wordMatrix221_expansion, wordMatrix099_expansion, mul_assoc]

def wordMatrix223 : QuotientMatrix := quotientDecode #v[1071, 3931, 2802, 723, 879, 3845, 578, 2263, 2342, 2402, 1702, 3021]

private theorem wordMatrix223_product : wordMatrix223 = wordMatrix050 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix223_expansion : wordMatrix223 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix223_product, wordMatrix050_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix224 : QuotientMatrix := quotientDecode #v[1376, 2938, 3894, 1690, 3954, 363, 3448, 3379, 823, 27, 3836, 212]

private theorem wordMatrix224_product : wordMatrix224 = wordMatrix043 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix224_expansion : wordMatrix224 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix224_product, wordMatrix043_expansion, wordMatrix009_expansion, mul_assoc]

def wordMatrix225 : QuotientMatrix := quotientDecode #v[2081, 1934, 1511, 312, 2185, 1874, 1561, 3777, 1732, 1162, 1779, 3967]

private theorem wordMatrix225_product : wordMatrix225 = wordMatrix223 * wordMatrix224 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix225_expansion : wordMatrix225 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix225_product, wordMatrix223_expansion, wordMatrix224_expansion, mul_assoc]

def wordMatrix226 : QuotientMatrix := quotientDecode #v[734, 3426, 2185, 3663, 4027, 3221, 4058, 600, 3844, 2399, 856, 1079]

private theorem wordMatrix226_product : wordMatrix226 = wordMatrix225 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix226_expansion : wordMatrix226 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix226_product, wordMatrix225_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix227 : QuotientMatrix := quotientDecode #v[2330, 2248, 33, 1657, 2661, 3300, 2560, 852, 484, 3064, 2780, 1519]

private theorem wordMatrix227_product : wordMatrix227 = wordMatrix012 * wordMatrix147 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix227_expansion : wordMatrix227 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix227_product, wordMatrix012_expansion, wordMatrix147_expansion, mul_assoc]

def wordMatrix228 : QuotientMatrix := quotientDecode #v[3752, 3117, 2439, 1828, 598, 671, 3995, 1774, 2705, 3496, 70, 3328]

private theorem wordMatrix228_product : wordMatrix228 = wordMatrix227 * wordMatrix044 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix228_expansion : wordMatrix228 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix228_product, wordMatrix227_expansion, wordMatrix044_expansion, mul_assoc]

def wordMatrix229 : QuotientMatrix := quotientDecode #v[3130, 3411, 4025, 3814, 1815, 625, 1446, 1473, 418, 1827, 3424, 2818]

private theorem wordMatrix229_product : wordMatrix229 = wordMatrix050 * wordMatrix001 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix229_expansion : wordMatrix229 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))) := by
  simp only [wordMatrix229_product, wordMatrix050_expansion, wordMatrix001_expansion, mul_assoc]

def wordMatrix230 : QuotientMatrix := quotientDecode #v[2071, 2422, 433, 1577, 1912, 1475, 3514, 1113, 717, 3734, 1868, 1984]

private theorem wordMatrix230_product : wordMatrix230 = wordMatrix228 * wordMatrix229 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix230_expansion : wordMatrix230 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix230_product, wordMatrix228_expansion, wordMatrix229_expansion, mul_assoc]

def wordMatrix231 : QuotientMatrix := quotientDecode #v[377, 419, 2468, 500, 2097, 3135, 2201, 1767, 3643, 1619, 3263, 459]

private theorem wordMatrix231_product : wordMatrix231 = wordMatrix066 * wordMatrix052 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix231_expansion : wordMatrix231 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix231_product, wordMatrix066_expansion, wordMatrix052_expansion, mul_assoc]

def wordMatrix232 : QuotientMatrix := quotientDecode #v[3960, 1209, 2181, 2244, 41, 2403, 1349, 2387, 2413, 4029, 3947, 958]

private theorem wordMatrix232_product : wordMatrix232 = wordMatrix045 * wordMatrix041 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix232_expansion : wordMatrix232 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))) := by
  simp only [wordMatrix232_product, wordMatrix045_expansion, wordMatrix041_expansion, mul_assoc]

def wordMatrix233 : QuotientMatrix := quotientDecode #v[734, 668, 614, 1204, 1420, 3615, 3448, 1767, 2343, 3707, 1868, 1662]

private theorem wordMatrix233_product : wordMatrix233 = wordMatrix231 * wordMatrix232 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix233_expansion : wordMatrix233 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))) := by
  simp only [wordMatrix233_product, wordMatrix231_expansion, wordMatrix232_expansion, mul_assoc]

def wordMatrix234 : QuotientMatrix := quotientDecode #v[1971, 1753, 299, 693, 2320, 4087, 1439, 2597, 4070, 2084, 1903, 1640]

private theorem wordMatrix234_product : wordMatrix234 = wordMatrix101 * wordMatrix021 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix234_expansion : wordMatrix234 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix234_product, wordMatrix101_expansion, wordMatrix021_expansion, mul_assoc]

def wordMatrix235 : QuotientMatrix := quotientDecode #v[1348, 1949, 1633, 3642, 3718, 3806, 2799, 823, 3382, 3630, 3398, 1110]

private theorem wordMatrix235_product : wordMatrix235 = wordMatrix234 * wordMatrix120 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix235_expansion : wordMatrix235 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix235_product, wordMatrix234_expansion, wordMatrix120_expansion, mul_assoc]

def wordMatrix236 : QuotientMatrix := quotientDecode #v[2069, 3883, 3494, 3598, 3024, 2020, 3512, 3626, 3322, 4084, 3513, 722]

private theorem wordMatrix236_product : wordMatrix236 = wordMatrix021 * wordMatrix145 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix236_expansion : wordMatrix236 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))) := by
  simp only [wordMatrix236_product, wordMatrix021_expansion, wordMatrix145_expansion, mul_assoc]

def wordMatrix237 : QuotientMatrix := quotientDecode #v[349, 240, 4, 3470, 3128, 1118, 3526, 1442, 3368, 3064, 3236, 2396]

private theorem wordMatrix237_product : wordMatrix237 = wordMatrix235 * wordMatrix236 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix237_expansion : wordMatrix237 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix237_product, wordMatrix235_expansion, wordMatrix236_expansion, mul_assoc]

def wordMatrix238 : QuotientMatrix := quotientDecode #v[3220, 1529, 3659, 2434, 158, 3365, 3873, 3410, 2098, 2300, 1506, 3491]

private theorem wordMatrix238_product : wordMatrix238 = wordMatrix018 * wordMatrix020 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix238_expansion : wordMatrix238 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))) := by
  simp only [wordMatrix238_product, wordMatrix018_expansion, wordMatrix020_expansion, mul_assoc]

def wordMatrix239 : QuotientMatrix := quotientDecode #v[455, 82, 3003, 2335, 2585, 776, 1840, 964, 937, 189, 511, 2303]

private theorem wordMatrix239_product : wordMatrix239 = wordMatrix238 * wordMatrix087 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix239_expansion : wordMatrix239 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix239_product, wordMatrix238_expansion, wordMatrix087_expansion, mul_assoc]

def wordMatrix240 : QuotientMatrix := quotientDecode #v[1388, 1460, 865, 3456, 3164, 649, 2238, 1078, 3430, 759, 9, 3490]

private theorem wordMatrix240_product : wordMatrix240 = wordMatrix128 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix240_expansion : wordMatrix240 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix240_product, wordMatrix128_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix241 : QuotientMatrix := quotientDecode #v[599, 342, 1416, 673, 3045, 529, 333, 120, 450, 366, 258, 454]

private theorem wordMatrix241_product : wordMatrix241 = wordMatrix239 * wordMatrix240 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix241_expansion : wordMatrix241 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix241_product, wordMatrix239_expansion, wordMatrix240_expansion, mul_assoc]

def wordMatrix242 : QuotientMatrix := quotientDecode #v[2972, 2524, 33, 1141, 4080, 1579, 3268, 2633, 1310, 180, 309, 1864]

private theorem wordMatrix242_product : wordMatrix242 = wordMatrix241 * wordMatrix099 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix242_expansion : wordMatrix242 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix242_product, wordMatrix241_expansion, wordMatrix099_expansion, mul_assoc]

def wordMatrix243 : QuotientMatrix := quotientDecode #v[1993, 1763, 2398, 2881, 1629, 2234, 1796, 2316, 69, 2026, 3409, 604]

private theorem wordMatrix243_product : wordMatrix243 = wordMatrix101 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix243_expansion : wordMatrix243 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix243_product, wordMatrix101_expansion, wordMatrix019_expansion, mul_assoc]

def wordMatrix244 : QuotientMatrix := quotientDecode #v[3581, 251, 376, 1936, 713, 2445, 3723, 2443, 2537, 4022, 2867, 882]

private theorem wordMatrix244_product : wordMatrix244 = wordMatrix076 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix244_expansion : wordMatrix244 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix244_product, wordMatrix076_expansion, wordMatrix019_expansion, mul_assoc]

def wordMatrix245 : QuotientMatrix := quotientDecode #v[1, 1806, 202, 1627, 978, 1750, 3092, 3187, 526, 1162, 23, 1308]

private theorem wordMatrix245_product : wordMatrix245 = wordMatrix243 * wordMatrix244 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix245_expansion : wordMatrix245 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix245_product, wordMatrix243_expansion, wordMatrix244_expansion, mul_assoc]

def wordMatrix246 : QuotientMatrix := quotientDecode #v[2735, 741, 45, 986, 876, 277, 503, 1237, 1119, 1052, 215, 2219]

private theorem wordMatrix246_product : wordMatrix246 = wordMatrix068 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix246_expansion : wordMatrix246 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix246_product, wordMatrix068_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix247 : QuotientMatrix := quotientDecode #v[502, 124, 764, 2294, 2660, 3017, 1043, 3085, 579, 883, 2388, 3012]

private theorem wordMatrix247_product : wordMatrix247 = wordMatrix050 * wordMatrix045 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix247_expansion : wordMatrix247 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix247_product, wordMatrix050_expansion, wordMatrix045_expansion, mul_assoc]

def wordMatrix248 : QuotientMatrix := quotientDecode #v[1267, 942, 53, 3008, 1248, 2861, 2182, 2084, 3235, 2362, 268, 1404]

private theorem wordMatrix248_product : wordMatrix248 = wordMatrix246 * wordMatrix247 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix248_expansion : wordMatrix248 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix248_product, wordMatrix246_expansion, wordMatrix247_expansion, mul_assoc]

def wordMatrix249 : QuotientMatrix := quotientDecode #v[1855, 534, 1590, 3467, 3718, 2713, 1675, 2434, 4029, 4003, 1175, 861]

private theorem wordMatrix249_product : wordMatrix249 = wordMatrix006 * wordMatrix048 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix249_expansion : wordMatrix249 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))) := by
  simp only [wordMatrix249_product, wordMatrix006_expansion, wordMatrix048_expansion, mul_assoc]

def wordMatrix250 : QuotientMatrix := quotientDecode #v[2728, 2734, 1302, 3146, 263, 1368, 3839, 4082, 504, 1890, 1024, 515]

private theorem wordMatrix250_product : wordMatrix250 = wordMatrix248 * wordMatrix249 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix250_expansion : wordMatrix250 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix250_product, wordMatrix248_expansion, wordMatrix249_expansion, mul_assoc]

def wordMatrix251 : QuotientMatrix := quotientDecode #v[3448, 3784, 4081, 1834, 1534, 3331, 3633, 260, 3334, 2298, 934, 3737]

private theorem wordMatrix251_product : wordMatrix251 = wordMatrix043 * wordMatrix032 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix251_expansion : wordMatrix251 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix251_product, wordMatrix043_expansion, wordMatrix032_expansion, mul_assoc]

def wordMatrix252 : QuotientMatrix := quotientDecode #v[101, 1831, 3250, 2597, 2091, 3882, 3590, 1086, 3492, 3336, 2609, 2079]

private theorem wordMatrix252_product : wordMatrix252 = wordMatrix251 * wordMatrix069 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix252_expansion : wordMatrix252 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix252_product, wordMatrix251_expansion, wordMatrix069_expansion, mul_assoc]

def wordMatrix253 : QuotientMatrix := quotientDecode #v[3581, 2077, 162, 757, 977, 2383, 722, 2285, 2006, 1104, 1292, 12]

private theorem wordMatrix253_product : wordMatrix253 = wordMatrix252 * wordMatrix048 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix253_expansion : wordMatrix253 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix253_product, wordMatrix252_expansion, wordMatrix048_expansion, mul_assoc]

def wordMatrix254 : QuotientMatrix := quotientDecode #v[1070, 2822, 2731, 405, 2078, 3466, 794, 2180, 3612, 4009, 1121, 540]

private theorem wordMatrix254_product : wordMatrix254 = wordMatrix030 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix254_expansion : wordMatrix254 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix254_product, wordMatrix030_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix255 : QuotientMatrix := quotientDecode #v[2783, 2201, 1405, 3261, 1416, 1459, 3773, 478, 2529, 2842, 631, 1376]

private theorem wordMatrix255_product : wordMatrix255 = wordMatrix004 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix255_expansion : wordMatrix255 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix255_product, wordMatrix004_expansion, wordMatrix009_expansion, mul_assoc]

def wordMatrix256 : QuotientMatrix := quotientDecode #v[1693, 2687, 1260, 533, 433, 2828, 855, 451, 69, 2019, 934, 1874]

private theorem wordMatrix256_product : wordMatrix256 = wordMatrix254 * wordMatrix255 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix256_expansion : wordMatrix256 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix256_product, wordMatrix254_expansion, wordMatrix255_expansion, mul_assoc]

def wordMatrix257 : QuotientMatrix := quotientDecode #v[2785, 2921, 1850, 3749, 33, 564, 2847, 3080, 117, 2281, 927, 3221]

private theorem wordMatrix257_product : wordMatrix257 = wordMatrix256 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix257_expansion : wordMatrix257 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix257_product, wordMatrix256_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix258 : QuotientMatrix := quotientDecode #v[3518, 65, 2553, 2993, 3691, 3921, 1048, 2576, 1775, 3721, 1659, 3806]

private theorem wordMatrix258_product : wordMatrix258 = wordMatrix032 * wordMatrix057 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix258_expansion : wordMatrix258 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix258_product, wordMatrix032_expansion, wordMatrix057_expansion, mul_assoc]

def wordMatrix259 : QuotientMatrix := quotientDecode #v[3983, 1462, 4, 221, 1740, 2243, 663, 36, 1181, 2826, 328, 2062]

private theorem wordMatrix259_product : wordMatrix259 = wordMatrix012 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix259_expansion : wordMatrix259 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))))))) := by
  simp only [wordMatrix259_product, wordMatrix012_expansion, mul_assoc]

def wordMatrix260 : QuotientMatrix := quotientDecode #v[1695, 3352, 3965, 1597, 764, 3333, 1881, 1480, 2770, 3386, 3134, 860]

private theorem wordMatrix260_product : wordMatrix260 = wordMatrix258 * wordMatrix259 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix260_expansion : wordMatrix260 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))))))))))))))))))))))) := by
  simp only [wordMatrix260_product, wordMatrix258_expansion, wordMatrix259_expansion, mul_assoc]

def wordMatrix261 : QuotientMatrix := quotientDecode #v[2249, 1721, 636, 1902, 1656, 720, 1208, 723, 1063, 3083, 1765, 1203]

private theorem wordMatrix261_product : wordMatrix261 = wordMatrix084 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix261_expansion : wordMatrix261 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX)))))))) := by
  simp only [wordMatrix261_product, wordMatrix084_expansion, mul_assoc]

def wordMatrix262 : QuotientMatrix := quotientDecode #v[2752, 101, 3435, 2342, 456, 784, 1209, 2886, 1737, 1825, 2616, 2271]

private theorem wordMatrix262_product : wordMatrix262 = wordMatrix143 * wordMatrix261 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix262_expansion : wordMatrix262 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))) := by
  simp only [wordMatrix262_product, wordMatrix143_expansion, wordMatrix261_expansion, mul_assoc]

def wordMatrix263 : QuotientMatrix := quotientDecode #v[3719, 2334, 1239, 1716, 1683, 824, 2014, 1442, 2137, 348, 1551, 129]

private theorem wordMatrix263_product : wordMatrix263 = wordMatrix007 * wordMatrix068 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix263_expansion : wordMatrix263 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix263_product, wordMatrix007_expansion, wordMatrix068_expansion, mul_assoc]

def wordMatrix264 : QuotientMatrix := quotientDecode #v[3973, 2738, 2902, 2949, 2512, 698, 811, 381, 2893, 1373, 2574, 54]

private theorem wordMatrix264_product : wordMatrix264 = wordMatrix068 * wordMatrix007 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix264_expansion : wordMatrix264 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix264_product, wordMatrix068_expansion, wordMatrix007_expansion, mul_assoc]

def wordMatrix265 : QuotientMatrix := quotientDecode #v[121, 2250, 4073, 3602, 713, 3839, 1529, 2102, 3789, 357, 2743, 3832]

private theorem wordMatrix265_product : wordMatrix265 = wordMatrix263 * wordMatrix264 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix265_expansion : wordMatrix265 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix265_product, wordMatrix263_expansion, wordMatrix264_expansion, mul_assoc]

def wordMatrix266 : QuotientMatrix := quotientDecode #v[416, 2560, 2998, 36, 433, 3006, 548, 1113, 4070, 72, 657, 74]

private theorem wordMatrix266_product : wordMatrix266 = wordMatrix001 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix266_expansion : wordMatrix266 = matrixY * (matrixX * (matrixYInv)) := by
  simp only [wordMatrix266_product, wordMatrix001_expansion, mul_assoc]

def wordMatrix267 : QuotientMatrix := quotientDecode #v[2948, 2410, 3348, 3720, 148, 2696, 1555, 3465, 2599, 2031, 2858, 2035]

private theorem wordMatrix267_product : wordMatrix267 = wordMatrix008 * wordMatrix266 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix267_expansion : wordMatrix267 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv)))))) := by
  simp only [wordMatrix267_product, wordMatrix008_expansion, wordMatrix266_expansion, mul_assoc]

def wordMatrix268 : QuotientMatrix := quotientDecode #v[2307, 2955, 1295, 712, 2425, 3010, 1415, 2449, 2228, 44, 2163, 1080]

private theorem wordMatrix268_product : wordMatrix268 = wordMatrix265 * wordMatrix267 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix268_expansion : wordMatrix268 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix268_product, wordMatrix265_expansion, wordMatrix267_expansion, mul_assoc]

def wordMatrix269 : QuotientMatrix := quotientDecode #v[2972, 2104, 3940, 1133, 1479, 3964, 1899, 1472, 3243, 2501, 2939, 171]

private theorem wordMatrix269_product : wordMatrix269 = wordMatrix128 * wordMatrix077 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix269_expansion : wordMatrix269 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix269_product, wordMatrix128_expansion, wordMatrix077_expansion, mul_assoc]

def wordMatrix270 : QuotientMatrix := quotientDecode #v[3945, 3714, 2859, 1552, 974, 1632, 1319, 317, 2336, 708, 1175, 1800]

private theorem wordMatrix270_product : wordMatrix270 = wordMatrix196 * wordMatrix269 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix270_expansion : wordMatrix270 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix270_product, wordMatrix196_expansion, wordMatrix269_expansion, mul_assoc]

def wordMatrix271 : QuotientMatrix := quotientDecode #v[2959, 3367, 591, 1538, 2585, 1554, 1759, 2737, 90, 2281, 1677, 360]

private theorem wordMatrix271_product : wordMatrix271 = wordMatrix270 * wordMatrix017 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix271_expansion : wordMatrix271 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix271_product, wordMatrix270_expansion, wordMatrix017_expansion, mul_assoc]

def wordMatrix272 : QuotientMatrix := quotientDecode #v[2752, 1712, 141, 1913, 2425, 146, 3563, 36, 4016, 4008, 3767, 2295]

private theorem wordMatrix272_product : wordMatrix272 = wordMatrix085 * wordMatrix087 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix272_expansion : wordMatrix272 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix272_product, wordMatrix085_expansion, wordMatrix087_expansion, mul_assoc]

def wordMatrix273 : QuotientMatrix := quotientDecode #v[1357, 926, 2124, 4014, 856, 3907, 1785, 2287, 180, 392, 176, 548]

private theorem wordMatrix273_product : wordMatrix273 = wordMatrix077 * wordMatrix096 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix273_expansion : wordMatrix273 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix273_product, wordMatrix077_expansion, wordMatrix096_expansion, mul_assoc]

def wordMatrix274 : QuotientMatrix := quotientDecode #v[3514, 1484, 2624, 397, 657, 2089, 2568, 1807, 1884, 2986, 2423, 3766]

private theorem wordMatrix274_product : wordMatrix274 = wordMatrix272 * wordMatrix273 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix274_expansion : wordMatrix274 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix274_product, wordMatrix272_expansion, wordMatrix273_expansion, mul_assoc]

def wordMatrix275 : QuotientMatrix := quotientDecode #v[2702, 1556, 1960, 887, 4062, 926, 2014, 2142, 1356, 197, 541, 3096]

private theorem wordMatrix275_product : wordMatrix275 = wordMatrix274 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix275_expansion : wordMatrix275 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix275_product, wordMatrix274_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix276 : QuotientMatrix := quotientDecode #v[1309, 3478, 3378, 2180, 987, 63, 3964, 3941, 3177, 1628, 1788, 87]

private theorem wordMatrix276_product : wordMatrix276 = wordMatrix030 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix276_expansion : wordMatrix276 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix276_product, wordMatrix030_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix277 : QuotientMatrix := quotientDecode #v[146, 2741, 2618, 750, 3659, 1639, 662, 1472, 1802, 1737, 2902, 2679]

private theorem wordMatrix277_product : wordMatrix277 = wordMatrix149 * wordMatrix276 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix277_expansion : wordMatrix277 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix277_product, wordMatrix149_expansion, wordMatrix276_expansion, mul_assoc]

def wordMatrix278 : QuotientMatrix := quotientDecode #v[2766, 1693, 3019, 2633, 884, 668, 4030, 2841, 3403, 1225, 1777, 1090]

private theorem wordMatrix278_product : wordMatrix278 = wordMatrix277 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix278_expansion : wordMatrix278 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix278_product, wordMatrix277_expansion, mul_assoc]

def wordMatrix279 : QuotientMatrix := quotientDecode #v[2680, 3607, 400, 2094, 25, 1459, 3984, 3534, 2648, 1045, 3893, 86]

private theorem wordMatrix279_product : wordMatrix279 = wordMatrix074 * wordMatrix074 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix279_expansion : wordMatrix279 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix279_product, wordMatrix074_expansion, mul_assoc]

def wordMatrix280 : QuotientMatrix := quotientDecode #v[1795, 1999, 1650, 3644, 2833, 63, 331, 347, 1374, 3141, 695, 3557]

private theorem wordMatrix280_product : wordMatrix280 = wordMatrix279 * wordMatrix143 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix280_expansion : wordMatrix280 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix280_product, wordMatrix279_expansion, wordMatrix143_expansion, mul_assoc]

def wordMatrix281 : QuotientMatrix := quotientDecode #v[1562, 1334, 135, 3529, 3807, 3337, 1886, 1087, 3712, 3944, 3290, 2656]

private theorem wordMatrix281_product : wordMatrix281 = wordMatrix084 * wordMatrix016 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix281_expansion : wordMatrix281 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))) := by
  simp only [wordMatrix281_product, wordMatrix084_expansion, wordMatrix016_expansion, mul_assoc]

def wordMatrix282 : QuotientMatrix := quotientDecode #v[3614, 49, 524, 1866, 845, 3508, 1851, 2532, 931, 1913, 2858, 207]

private theorem wordMatrix282_product : wordMatrix282 = wordMatrix280 * wordMatrix281 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix282_expansion : wordMatrix282 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix282_product, wordMatrix280_expansion, wordMatrix281_expansion, mul_assoc]

def wordMatrix283 : QuotientMatrix := quotientDecode #v[2704, 2149, 105, 316, 664, 1208, 1750, 2523, 2856, 2767, 3439, 4040]

private theorem wordMatrix283_product : wordMatrix283 = wordMatrix207 * wordMatrix148 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix283_expansion : wordMatrix283 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix283_product, wordMatrix207_expansion, wordMatrix148_expansion, mul_assoc]

def wordMatrix284 : QuotientMatrix := quotientDecode #v[3066, 3111, 1702, 4065, 3605, 3221, 1445, 3545, 2984, 1689, 1092, 3081]

private theorem wordMatrix284_product : wordMatrix284 = wordMatrix283 * wordMatrix006 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix284_expansion : wordMatrix284 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix284_product, wordMatrix283_expansion, wordMatrix006_expansion, mul_assoc]

def wordMatrix285 : QuotientMatrix := quotientDecode #v[2898, 760, 3024, 3334, 3759, 2750, 3023, 733, 2927, 1532, 2520, 3956]

private theorem wordMatrix285_product : wordMatrix285 = wordMatrix068 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix285_expansion : wordMatrix285 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix285_product, wordMatrix068_expansion, wordMatrix004_expansion, mul_assoc]

def wordMatrix286 : QuotientMatrix := quotientDecode #v[2035, 599, 1906, 2599, 1708, 1847, 3393, 2564, 2006, 4036, 1337, 2515]

private theorem wordMatrix286_product : wordMatrix286 = wordMatrix032 * wordMatrix147 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix286_expansion : wordMatrix286 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix286_product, wordMatrix032_expansion, wordMatrix147_expansion, mul_assoc]

def wordMatrix287 : QuotientMatrix := quotientDecode #v[2171, 829, 40, 3609, 1772, 650, 3701, 1163, 838, 2404, 1483, 3920]

private theorem wordMatrix287_product : wordMatrix287 = wordMatrix285 * wordMatrix286 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix287_expansion : wordMatrix287 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix287_product, wordMatrix285_expansion, wordMatrix286_expansion, mul_assoc]

def wordMatrix288 : QuotientMatrix := quotientDecode #v[168, 1847, 1314, 733, 3283, 3396, 830, 787, 3720, 4065, 3589, 785]

private theorem wordMatrix288_product : wordMatrix288 = wordMatrix287 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix288_expansion : wordMatrix288 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix288_product, wordMatrix287_expansion, mul_assoc]

def wordMatrix289 : QuotientMatrix := quotientDecode #v[389, 1718, 3127, 2459, 1916, 3563, 3186, 1056, 3834, 3351, 810, 2818]

private theorem wordMatrix289_product : wordMatrix289 = wordMatrix101 * wordMatrix077 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix289_expansion : wordMatrix289 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix289_product, wordMatrix101_expansion, wordMatrix077_expansion, mul_assoc]

def wordMatrix290 : QuotientMatrix := quotientDecode #v[3649, 2489, 2852, 1857, 3094, 10, 4061, 809, 1193, 3880, 3161, 3390]

private theorem wordMatrix290_product : wordMatrix290 = wordMatrix084 * wordMatrix238 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix290_expansion : wordMatrix290 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix290_product, wordMatrix084_expansion, wordMatrix238_expansion, mul_assoc]

def wordMatrix291 : QuotientMatrix := quotientDecode #v[741, 3801, 423, 1553, 2172, 2441, 2847, 3155, 95, 1284, 1395, 3846]

private theorem wordMatrix291_product : wordMatrix291 = wordMatrix289 * wordMatrix290 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix291_expansion : wordMatrix291 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix291_product, wordMatrix289_expansion, wordMatrix290_expansion, mul_assoc]

def wordMatrix292 : QuotientMatrix := quotientDecode #v[2631, 2812, 1810, 2987, 2503, 401, 3713, 837, 229, 945, 107, 2712]

private theorem wordMatrix292_product : wordMatrix292 = wordMatrix291 * wordMatrix122 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix292_expansion : wordMatrix292 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix292_product, wordMatrix291_expansion, wordMatrix122_expansion, mul_assoc]

def wordMatrix293 : QuotientMatrix := quotientDecode #v[3451, 3863, 1954, 693, 1600, 1925, 566, 3721, 2005, 945, 2636, 3120]

private theorem wordMatrix293_product : wordMatrix293 = wordMatrix074 * wordMatrix096 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix293_expansion : wordMatrix293 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix293_product, wordMatrix074_expansion, wordMatrix096_expansion, mul_assoc]

def wordMatrix294 : QuotientMatrix := quotientDecode #v[2866, 408, 2624, 3763, 3955, 264, 1974, 102, 638, 597, 2663, 505]

private theorem wordMatrix294_product : wordMatrix294 = wordMatrix103 * wordMatrix293 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix294_expansion : wordMatrix294 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix294_product, wordMatrix103_expansion, wordMatrix293_expansion, mul_assoc]

def wordMatrix295 : QuotientMatrix := quotientDecode #v[3896, 553, 2374, 2387, 2988, 3189, 3387, 1152, 2346, 1006, 3045, 3562]

private theorem wordMatrix295_product : wordMatrix295 = wordMatrix294 * wordMatrix145 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix295_expansion : wordMatrix295 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix295_product, wordMatrix294_expansion, wordMatrix145_expansion, mul_assoc]

def wordMatrix296 : QuotientMatrix := quotientDecode #v[993, 2972, 598, 102, 1863, 972, 1068, 890, 1699, 474, 258, 1393]

private theorem wordMatrix296_product : wordMatrix296 = wordMatrix096 * wordMatrix074 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix296_expansion : wordMatrix296 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix296_product, wordMatrix096_expansion, wordMatrix074_expansion, mul_assoc]

def wordMatrix297 : QuotientMatrix := quotientDecode #v[3014, 1806, 3955, 3386, 4092, 3977, 2366, 2613, 1505, 1442, 1919, 2409]

private theorem wordMatrix297_product : wordMatrix297 = wordMatrix238 * wordMatrix238 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix297_expansion : wordMatrix297 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix297_product, wordMatrix238_expansion, mul_assoc]

def wordMatrix298 : QuotientMatrix := quotientDecode #v[1799, 3754, 2845, 3786, 3513, 257, 2751, 828, 2985, 802, 751, 19]

private theorem wordMatrix298_product : wordMatrix298 = wordMatrix296 * wordMatrix297 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix298_expansion : wordMatrix298 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix298_product, wordMatrix296_expansion, wordMatrix297_expansion, mul_assoc]

def wordMatrix299 : QuotientMatrix := quotientDecode #v[3206, 3166, 1171, 486, 2320, 2874, 2707, 736, 768, 762, 3494, 3783]

private theorem wordMatrix299_product : wordMatrix299 = wordMatrix085 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix299_expansion : wordMatrix299 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))) := by
  simp only [wordMatrix299_product, wordMatrix085_expansion, mul_assoc]

def wordMatrix300 : QuotientMatrix := quotientDecode #v[2071, 1529, 4062, 1104, 3531, 3974, 2394, 1701, 2951, 1694, 1054, 2504]

private theorem wordMatrix300_product : wordMatrix300 = wordMatrix298 * wordMatrix299 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix300_expansion : wordMatrix300 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix300_product, wordMatrix298_expansion, wordMatrix299_expansion, mul_assoc]

def wordMatrix301 : QuotientMatrix := quotientDecode #v[121, 2250, 1280, 1654, 3127, 3839, 2832, 1736, 702, 1023, 2720, 2146]

private theorem wordMatrix301_product : wordMatrix301 = wordMatrix045 * wordMatrix066 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix301_expansion : wordMatrix301 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix301_product, wordMatrix045_expansion, wordMatrix066_expansion, mul_assoc]

def wordMatrix302 : QuotientMatrix := quotientDecode #v[1167, 3899, 323, 2946, 2435, 2543, 2568, 2561, 782, 2639, 1772, 778]

private theorem wordMatrix302_product : wordMatrix302 = wordMatrix030 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix302_expansion : wordMatrix302 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix302_product, wordMatrix030_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix303 : QuotientMatrix := quotientDecode #v[1385, 1978, 1506, 2239, 3965, 3769, 968, 1832, 1496, 2129, 2731, 4054]

private theorem wordMatrix303_product : wordMatrix303 = wordMatrix301 * wordMatrix302 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix303_expansion : wordMatrix303 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix303_product, wordMatrix301_expansion, wordMatrix302_expansion, mul_assoc]

def wordMatrix304 : QuotientMatrix := quotientDecode #v[2476, 548, 3536, 3597, 330, 2219, 2015, 2662, 3116, 39, 2308, 2921]

private theorem wordMatrix304_product : wordMatrix304 = wordMatrix012 * wordMatrix001 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix304_expansion : wordMatrix304 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))) := by
  simp only [wordMatrix304_product, wordMatrix012_expansion, wordMatrix001_expansion, mul_assoc]

def wordMatrix305 : QuotientMatrix := quotientDecode #v[3581, 2721, 542, 187, 2601, 1644, 4031, 937, 2006, 1104, 3078, 3425]

private theorem wordMatrix305_product : wordMatrix305 = wordMatrix303 * wordMatrix304 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix305_expansion : wordMatrix305 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix305_product, wordMatrix303_expansion, wordMatrix304_expansion, mul_assoc]

def wordMatrix306 : QuotientMatrix := quotientDecode #v[267, 3483, 3030, 1808, 2165, 3578, 2139, 3259, 608, 798, 403, 3722]

private theorem wordMatrix306_product : wordMatrix306 = wordMatrix004 * wordMatrix068 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix306_expansion : wordMatrix306 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix306_product, wordMatrix004_expansion, wordMatrix068_expansion, mul_assoc]

def wordMatrix307 : QuotientMatrix := quotientDecode #v[3818, 2603, 3568, 685, 963, 2914, 468, 1849, 1817, 1480, 2655, 3363]

private theorem wordMatrix307_product : wordMatrix307 = wordMatrix032 * wordMatrix066 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix307_expansion : wordMatrix307 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix307_product, wordMatrix032_expansion, wordMatrix066_expansion, mul_assoc]

def wordMatrix308 : QuotientMatrix := quotientDecode #v[373, 755, 3335, 2893, 1868, 1711, 2392, 3720, 3966, 1124, 1826, 3339]

private theorem wordMatrix308_product : wordMatrix308 = wordMatrix306 * wordMatrix307 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix308_expansion : wordMatrix308 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix308_product, wordMatrix306_expansion, wordMatrix307_expansion, mul_assoc]

def wordMatrix309 : QuotientMatrix := quotientDecode #v[3104, 412, 2920, 2378, 2495, 1723, 2406, 3168, 3307, 3763, 3078, 213]

private theorem wordMatrix309_product : wordMatrix309 = wordMatrix308 * wordMatrix249 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix309_expansion : wordMatrix309 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix309_product, wordMatrix308_expansion, wordMatrix249_expansion, mul_assoc]

def wordMatrix310 : QuotientMatrix := quotientDecode #v[3801, 455, 868, 3179, 3419, 1254, 4055, 337, 1958, 1428, 1528, 2708]

private theorem wordMatrix310_product : wordMatrix310 = wordMatrix080 * wordMatrix238 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix310_expansion : wordMatrix310 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix310_product, wordMatrix080_expansion, wordMatrix238_expansion, mul_assoc]

def wordMatrix311 : QuotientMatrix := quotientDecode #v[2696, 704, 541, 1038, 542, 496, 1298, 1435, 1013, 2227, 2989, 1549]

private theorem wordMatrix311_product : wordMatrix311 = wordMatrix310 * wordMatrix269 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix311_expansion : wordMatrix311 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix311_product, wordMatrix310_expansion, wordMatrix269_expansion, mul_assoc]

def wordMatrix312 : QuotientMatrix := quotientDecode #v[149, 1556, 845, 3097, 1216, 1662, 2177, 1273, 2522, 1312, 904, 1996]

private theorem wordMatrix312_product : wordMatrix312 = wordMatrix311 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix312_expansion : wordMatrix312 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix312_product, wordMatrix311_expansion, mul_assoc]

def wordMatrix313 : QuotientMatrix := quotientDecode #v[928, 505, 1280, 3852, 2527, 1452, 1115, 3693, 382, 1789, 396, 1798]

private theorem wordMatrix313_product : wordMatrix313 = wordMatrix076 * wordMatrix080 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix313_expansion : wordMatrix313 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix313_product, wordMatrix076_expansion, wordMatrix080_expansion, mul_assoc]

def wordMatrix314 : QuotientMatrix := quotientDecode #v[3658, 3578, 2936, 1394, 3392, 968, 510, 2856, 3272, 2762, 1650, 2851]

private theorem wordMatrix314_product : wordMatrix314 = wordMatrix297 * wordMatrix313 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix314_expansion : wordMatrix314 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix314_product, wordMatrix297_expansion, wordMatrix313_expansion, mul_assoc]

def wordMatrix315 : QuotientMatrix := quotientDecode #v[1115, 2317, 3283, 1100, 137, 3669, 446, 2600, 1336, 486, 644, 3846]

private theorem wordMatrix315_product : wordMatrix315 = wordMatrix314 * wordMatrix018 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix315_expansion : wordMatrix315 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix315_product, wordMatrix314_expansion, wordMatrix018_expansion, mul_assoc]

def wordMatrix316 : QuotientMatrix := quotientDecode #v[1971, 97, 3802, 937, 127, 960, 343, 1537, 364, 3418, 2512, 3735]

private theorem wordMatrix316_product : wordMatrix316 = wordMatrix087 * wordMatrix021 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix316_expansion : wordMatrix316 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix316_product, wordMatrix087_expansion, wordMatrix021_expansion, mul_assoc]

def wordMatrix317 : QuotientMatrix := quotientDecode #v[1836, 161, 1416, 827, 2827, 3347, 3768, 2917, 361, 2701, 1175, 281]

private theorem wordMatrix317_product : wordMatrix317 = wordMatrix073 * wordMatrix238 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix317_expansion : wordMatrix317 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix317_product, wordMatrix073_expansion, wordMatrix238_expansion, mul_assoc]

def wordMatrix318 : QuotientMatrix := quotientDecode #v[1411, 1159, 591, 2437, 2462, 3641, 1759, 2358, 1137, 718, 3750, 3432]

private theorem wordMatrix318_product : wordMatrix318 = wordMatrix316 * wordMatrix317 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix318_expansion : wordMatrix318 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix318_product, wordMatrix316_expansion, wordMatrix317_expansion, mul_assoc]

def wordMatrix319 : QuotientMatrix := quotientDecode #v[3194, 2898, 1722, 3789, 2936, 1153, 566, 3403, 2204, 2298, 25, 3675]

private theorem wordMatrix319_product : wordMatrix319 = wordMatrix023 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix319_expansion : wordMatrix319 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))) := by
  simp only [wordMatrix319_product, wordMatrix023_expansion, mul_assoc]

def wordMatrix320 : QuotientMatrix := quotientDecode #v[742, 3264, 1427, 332, 977, 3062, 953, 1238, 428, 1186, 666, 3748]

private theorem wordMatrix320_product : wordMatrix320 = wordMatrix318 * wordMatrix319 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix320_expansion : wordMatrix320 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix320_product, wordMatrix318_expansion, wordMatrix319_expansion, mul_assoc]

def wordMatrix321 : QuotientMatrix := quotientDecode #v[443, 2853, 4046, 3789, 1903, 3014, 3727, 3814, 3561, 3237, 1852, 2100]

private theorem wordMatrix321_product : wordMatrix321 = wordMatrix012 * wordMatrix057 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix321_expansion : wordMatrix321 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix321_product, wordMatrix012_expansion, wordMatrix057_expansion, mul_assoc]

def wordMatrix322 : QuotientMatrix := quotientDecode #v[2797, 1287, 998, 2639, 75, 1609, 1579, 474, 2575, 2085, 1919, 794]

private theorem wordMatrix322_product : wordMatrix322 = wordMatrix004 * wordMatrix002 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix322_expansion : wordMatrix322 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))) := by
  simp only [wordMatrix322_product, wordMatrix004_expansion, wordMatrix002_expansion, mul_assoc]

def wordMatrix323 : QuotientMatrix := quotientDecode #v[2162, 3698, 3344, 2293, 884, 32, 3033, 2841, 3952, 2813, 2814, 1790]

private theorem wordMatrix323_product : wordMatrix323 = wordMatrix321 * wordMatrix322 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix323_expansion : wordMatrix323 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))) := by
  simp only [wordMatrix323_product, wordMatrix321_expansion, wordMatrix322_expansion, mul_assoc]

def wordMatrix324 : QuotientMatrix := quotientDecode #v[79, 1721, 2740, 672, 1660, 1199, 3925, 2739, 3163, 750, 3398, 1864]

private theorem wordMatrix324_product : wordMatrix324 = wordMatrix052 * wordMatrix052 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix324_expansion : wordMatrix324 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix324_product, wordMatrix052_expansion, mul_assoc]

def wordMatrix325 : QuotientMatrix := quotientDecode #v[2004, 907, 884, 2224, 125, 195, 2595, 1636, 508, 790, 299, 832]

private theorem wordMatrix325_product : wordMatrix325 = wordMatrix012 * wordMatrix030 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix325_expansion : wordMatrix325 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix325_product, wordMatrix012_expansion, wordMatrix030_expansion, mul_assoc]

def wordMatrix326 : QuotientMatrix := quotientDecode #v[1464, 2947, 1528, 1457, 868, 2071, 3711, 723, 1242, 2013, 2379, 338]

private theorem wordMatrix326_product : wordMatrix326 = wordMatrix324 * wordMatrix325 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix326_expansion : wordMatrix326 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix326_product, wordMatrix324_expansion, wordMatrix325_expansion, mul_assoc]

def wordMatrix327 : QuotientMatrix := quotientDecode #v[170, 2445, 70, 2467, 1642, 924, 390, 1866, 3677, 750, 1216, 343]

private theorem wordMatrix327_product : wordMatrix327 = wordMatrix326 * wordMatrix147 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix327_expansion : wordMatrix327 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix327_product, wordMatrix326_expansion, wordMatrix147_expansion, mul_assoc]

def wordMatrix328 : QuotientMatrix := quotientDecode #v[1719, 150, 2487, 1059, 2819, 1883, 2602, 563, 2026, 1168, 2998, 3220]

private theorem wordMatrix328_product : wordMatrix328 = wordMatrix057 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix328_expansion : wordMatrix328 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix328_product, wordMatrix057_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix329 : QuotientMatrix := quotientDecode #v[1338, 232, 961, 2005, 246, 578, 469, 767, 3384, 1657, 2676, 2479]

private theorem wordMatrix329_product : wordMatrix329 = wordMatrix030 * wordMatrix052 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix329_expansion : wordMatrix329 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix329_product, wordMatrix030_expansion, wordMatrix052_expansion, mul_assoc]

def wordMatrix330 : QuotientMatrix := quotientDecode #v[2645, 288, 719, 3556, 1852, 529, 2729, 287, 1888, 2173, 396, 531]

private theorem wordMatrix330_product : wordMatrix330 = wordMatrix328 * wordMatrix329 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix330_expansion : wordMatrix330 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix330_product, wordMatrix328_expansion, wordMatrix329_expansion, mul_assoc]

def wordMatrix331 : QuotientMatrix := quotientDecode #v[758, 1464, 4025, 3374, 1941, 2680, 3239, 1461, 3305, 3953, 995, 3117]

private theorem wordMatrix331_product : wordMatrix331 = wordMatrix006 * wordMatrix001 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix331_expansion : wordMatrix331 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))) := by
  simp only [wordMatrix331_product, wordMatrix006_expansion, wordMatrix001_expansion, mul_assoc]

def wordMatrix332 : QuotientMatrix := quotientDecode #v[1313, 1681, 954, 4084, 3841, 2578, 841, 3749, 1700, 3334, 3019, 4010]

private theorem wordMatrix332_product : wordMatrix332 = wordMatrix330 * wordMatrix331 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix332_expansion : wordMatrix332 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix332_product, wordMatrix330_expansion, wordMatrix331_expansion, mul_assoc]

def wordMatrix333 : QuotientMatrix := quotientDecode #v[1778, 3054, 3589, 1782, 1539, 2657, 849, 2718, 1577, 2694, 2261, 584]

private theorem wordMatrix333_product : wordMatrix333 = wordMatrix066 * wordMatrix038 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix333_expansion : wordMatrix333 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix333_product, wordMatrix066_expansion, wordMatrix038_expansion, mul_assoc]

def wordMatrix334 : QuotientMatrix := quotientDecode #v[3585, 1925, 1985, 774, 1548, 493, 3909, 2297, 637, 1716, 3458, 1201]

private theorem wordMatrix334_product : wordMatrix334 = wordMatrix038 * wordMatrix038 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix334_expansion : wordMatrix334 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix334_product, wordMatrix038_expansion, mul_assoc]

def wordMatrix335 : QuotientMatrix := quotientDecode #v[3310, 1387, 1607, 2863, 690, 684, 897, 4018, 2012, 2744, 3265, 2807]

private theorem wordMatrix335_product : wordMatrix335 = wordMatrix333 * wordMatrix334 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix335_expansion : wordMatrix335 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix335_product, wordMatrix333_expansion, wordMatrix334_expansion, mul_assoc]

def wordMatrix336 : QuotientMatrix := quotientDecode #v[3135, 509, 3344, 1448, 3306, 1155, 3000, 571, 24, 1894, 376, 77]

private theorem wordMatrix336_product : wordMatrix336 = wordMatrix006 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix336_expansion : wordMatrix336 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY)))) := by
  simp only [wordMatrix336_product, wordMatrix006_expansion, mul_assoc]

def wordMatrix337 : QuotientMatrix := quotientDecode #v[1392, 1585, 3444, 1738, 3273, 2406, 2426, 3556, 3031, 2257, 1161, 1555]

private theorem wordMatrix337_product : wordMatrix337 = wordMatrix335 * wordMatrix336 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix337_expansion : wordMatrix337 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix337_product, wordMatrix335_expansion, wordMatrix336_expansion, mul_assoc]

def wordMatrix338 : QuotientMatrix := quotientDecode #v[1635, 860, 2116, 2365, 3564, 4019, 2001, 2625, 3610, 1218, 2446, 1201]

private theorem wordMatrix338_product : wordMatrix338 = wordMatrix073 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix338_expansion : wordMatrix338 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix338_product, wordMatrix073_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix339 : QuotientMatrix := quotientDecode #v[529, 319, 745, 2063, 2444, 122, 3274, 314, 1869, 3083, 2989, 3902]

private theorem wordMatrix339_product : wordMatrix339 = wordMatrix084 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix339_expansion : wordMatrix339 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix339_product, wordMatrix084_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix340 : QuotientMatrix := quotientDecode #v[2104, 1254, 285, 2418, 1202, 1079, 1670, 3566, 2084, 1890, 656, 368]

private theorem wordMatrix340_product : wordMatrix340 = wordMatrix338 * wordMatrix339 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix340_expansion : wordMatrix340 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix340_product, wordMatrix338_expansion, wordMatrix339_expansion, mul_assoc]

def wordMatrix341 : QuotientMatrix := quotientDecode #v[3974, 3070, 3103, 3438, 2715, 3466, 3754, 3645, 2321, 3539, 1653, 211]

private theorem wordMatrix341_product : wordMatrix341 = wordMatrix340 * wordMatrix132 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix341_expansion : wordMatrix341 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix341_product, wordMatrix340_expansion, wordMatrix132_expansion, mul_assoc]

def wordMatrix342 : QuotientMatrix := quotientDecode #v[2410, 3594, 3271, 959, 1762, 1625, 3194, 672, 686, 407, 2833, 373]

private theorem wordMatrix342_product : wordMatrix342 = wordMatrix045 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix342_expansion : wordMatrix342 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix342_product, wordMatrix045_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix343 : QuotientMatrix := quotientDecode #v[138, 2697, 1074, 873, 3954, 761, 2307, 3404, 838, 2796, 1146, 863]

private theorem wordMatrix343_product : wordMatrix343 = wordMatrix043 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix343_expansion : wordMatrix343 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix343_product, wordMatrix043_expansion, mul_assoc]

def wordMatrix344 : QuotientMatrix := quotientDecode #v[515, 1065, 3419, 1077, 681, 2820, 2637, 1369, 2187, 3913, 1293, 886]

private theorem wordMatrix344_product : wordMatrix344 = wordMatrix342 * wordMatrix343 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix344_expansion : wordMatrix344 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix344_product, wordMatrix342_expansion, wordMatrix343_expansion, mul_assoc]

def wordMatrix345 : QuotientMatrix := quotientDecode #v[454, 2046, 2844, 2581, 4056, 104, 1663, 616, 2584, 3872, 1161, 2912]

private theorem wordMatrix345_product : wordMatrix345 = wordMatrix344 * wordMatrix030 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix345_expansion : wordMatrix345 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix345_product, wordMatrix344_expansion, wordMatrix030_expansion, mul_assoc]

def wordMatrix346 : QuotientMatrix := quotientDecode #v[806, 1570, 3161, 1322, 2512, 3093, 2183, 3565, 1489, 3009, 3853, 3754]

private theorem wordMatrix346_product : wordMatrix346 = wordMatrix030 * wordMatrix068 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix346_expansion : wordMatrix346 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix346_product, wordMatrix030_expansion, wordMatrix068_expansion, mul_assoc]

def wordMatrix347 : QuotientMatrix := quotientDecode #v[360, 3411, 258, 2152, 1067, 1571, 2194, 1369, 3374, 3953, 2388, 1012]

private theorem wordMatrix347_product : wordMatrix347 = wordMatrix012 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix347_expansion : wordMatrix347 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix347_product, wordMatrix012_expansion, wordMatrix004_expansion, mul_assoc]

def wordMatrix348 : QuotientMatrix := quotientDecode #v[2093, 3413, 3865, 1890, 1850, 3809, 2964, 1124, 3314, 3336, 253, 912]

private theorem wordMatrix348_product : wordMatrix348 = wordMatrix346 * wordMatrix347 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix348_expansion : wordMatrix348 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix348_product, wordMatrix346_expansion, wordMatrix347_expansion, mul_assoc]

def wordMatrix349 : QuotientMatrix := quotientDecode #v[773, 1263, 2318, 3124, 45, 212, 1070, 2863, 3567, 4078, 1906, 2080]

private theorem wordMatrix349_product : wordMatrix349 = wordMatrix348 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix349_expansion : wordMatrix349 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix349_product, wordMatrix348_expansion, mul_assoc]

def wordMatrix350 : QuotientMatrix := quotientDecode #v[1599, 821, 41, 3489, 3934, 259, 829, 1131, 1244, 1028, 893, 1806]

private theorem wordMatrix350_product : wordMatrix350 = wordMatrix032 * wordMatrix052 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix350_expansion : wordMatrix350 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix350_product, wordMatrix032_expansion, wordMatrix052_expansion, mul_assoc]

def wordMatrix351 : QuotientMatrix := quotientDecode #v[2196, 3863, 1202, 3814, 2313, 47, 605, 2507, 2098, 765, 1542, 3806]

private theorem wordMatrix351_product : wordMatrix351 = wordMatrix009 * wordMatrix066 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix351_expansion : wordMatrix351 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix351_product, wordMatrix009_expansion, wordMatrix066_expansion, mul_assoc]

def wordMatrix352 : QuotientMatrix := quotientDecode #v[10, 4047, 1629, 410, 3072, 4017, 297, 3345, 3789, 692, 884, 2442]

private theorem wordMatrix352_product : wordMatrix352 = wordMatrix350 * wordMatrix351 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix352_expansion : wordMatrix352 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix352_product, wordMatrix350_expansion, wordMatrix351_expansion, mul_assoc]

def wordMatrix353 : QuotientMatrix := quotientDecode #v[1387, 1426, 2740, 395, 856, 1924, 2394, 2994, 1775, 2150, 327, 2889]

private theorem wordMatrix353_product : wordMatrix353 = wordMatrix052 * wordMatrix001 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix353_expansion : wordMatrix353 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))) := by
  simp only [wordMatrix353_product, wordMatrix052_expansion, wordMatrix001_expansion, mul_assoc]

def wordMatrix354 : QuotientMatrix := quotientDecode #v[1049, 3497, 3447, 2588, 2574, 3714, 1419, 2770, 3796, 3516, 2491, 525]

private theorem wordMatrix354_product : wordMatrix354 = wordMatrix352 * wordMatrix353 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix354_expansion : wordMatrix354 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix354_product, wordMatrix352_expansion, wordMatrix353_expansion, mul_assoc]

def wordMatrix355 : QuotientMatrix := quotientDecode #v[722, 60, 1656, 3815, 2509, 1339, 1644, 1761, 411, 1931, 253, 2111]

private theorem wordMatrix355_product : wordMatrix355 = wordMatrix302 * wordMatrix231 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix355_expansion : wordMatrix355 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix355_product, wordMatrix302_expansion, wordMatrix231_expansion, mul_assoc]

def wordMatrix356 : QuotientMatrix := quotientDecode #v[1746, 3227, 3807, 3834, 2655, 581, 4002, 2351, 1435, 2619, 1906, 3158]

private theorem wordMatrix356_product : wordMatrix356 = wordMatrix355 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix356_expansion : wordMatrix356 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix356_product, wordMatrix355_expansion, mul_assoc]

def wordMatrix357 : QuotientMatrix := quotientDecode #v[1326, 168, 1241, 3915, 3392, 1989, 4079, 1789, 3528, 395, 1409, 3926]

private theorem wordMatrix357_product : wordMatrix357 = wordMatrix085 * wordMatrix074 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix357_expansion : wordMatrix357 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix357_product, wordMatrix085_expansion, wordMatrix074_expansion, mul_assoc]

def wordMatrix358 : QuotientMatrix := quotientDecode #v[3017, 817, 2073, 2180, 3860, 3091, 349, 2361, 2893, 750, 1295, 447]

private theorem wordMatrix358_product : wordMatrix358 = wordMatrix074 * wordMatrix021 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix358_expansion : wordMatrix358 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix358_product, wordMatrix074_expansion, wordMatrix021_expansion, mul_assoc]

def wordMatrix359 : QuotientMatrix := quotientDecode #v[509, 3502, 306, 3122, 3744, 1816, 257, 2006, 3869, 520, 3250, 2162]

private theorem wordMatrix359_product : wordMatrix359 = wordMatrix357 * wordMatrix358 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix359_expansion : wordMatrix359 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix359_product, wordMatrix357_expansion, wordMatrix358_expansion, mul_assoc]

def wordMatrix360 : QuotientMatrix := quotientDecode #v[773, 50, 2553, 1513, 927, 4063, 399, 3418, 2984, 321, 1903, 1796]

private theorem wordMatrix360_product : wordMatrix360 = wordMatrix359 * wordMatrix017 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix360_expansion : wordMatrix360 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix360_product, wordMatrix359_expansion, wordMatrix017_expansion, mul_assoc]

def wordMatrix361 : QuotientMatrix := quotientDecode #v[2847, 3483, 1416, 2229, 1136, 2605, 1196, 3022, 2558, 2532, 1873, 3557]

private theorem wordMatrix361_product : wordMatrix361 = wordMatrix032 * wordMatrix036 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix361_expansion : wordMatrix361 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix361_product, wordMatrix032_expansion, wordMatrix036_expansion, mul_assoc]

def wordMatrix362 : QuotientMatrix := quotientDecode #v[480, 2837, 1018, 655, 2520, 2460, 3001, 1967, 1598, 763, 3036, 463]

private theorem wordMatrix362_product : wordMatrix362 = wordMatrix032 * wordMatrix032 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix362_expansion : wordMatrix362 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix362_product, wordMatrix032_expansion, mul_assoc]

def wordMatrix363 : QuotientMatrix := quotientDecode #v[1874, 2592, 2242, 1086, 33, 2621, 1178, 892, 451, 385, 3224, 3005]

private theorem wordMatrix363_product : wordMatrix363 = wordMatrix361 * wordMatrix362 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix363_expansion : wordMatrix363 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix363_product, wordMatrix361_expansion, wordMatrix362_expansion, mul_assoc]

def wordMatrix364 : QuotientMatrix := quotientDecode #v[3896, 2420, 4080, 2561, 237, 1624, 239, 2294, 247, 1814, 3646, 1557]

private theorem wordMatrix364_product : wordMatrix364 = wordMatrix363 * wordMatrix000 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix364_expansion : wordMatrix364 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix364_product, wordMatrix363_expansion, wordMatrix000_expansion, mul_assoc]

def wordMatrix365 : QuotientMatrix := quotientDecode #v[3315, 826, 3889, 2591, 263, 1733, 4017, 2643, 1668, 1982, 456, 867]

private theorem wordMatrix365_product : wordMatrix365 = wordMatrix050 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix365_expansion : wordMatrix365 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix365_product, wordMatrix050_expansion, wordMatrix004_expansion, mul_assoc]

def wordMatrix366 : QuotientMatrix := quotientDecode #v[1961, 741, 1328, 3621, 492, 570, 1780, 1052, 3515, 201, 713, 2890]

private theorem wordMatrix366_product : wordMatrix366 = wordMatrix068 * wordMatrix032 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix366_expansion : wordMatrix366 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix366_product, wordMatrix068_expansion, wordMatrix032_expansion, mul_assoc]

def wordMatrix367 : QuotientMatrix := quotientDecode #v[3569, 612, 142, 1078, 3527, 625, 1170, 2519, 812, 385, 374, 3312]

private theorem wordMatrix367_product : wordMatrix367 = wordMatrix365 * wordMatrix366 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix367_expansion : wordMatrix367 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix367_product, wordMatrix365_expansion, wordMatrix366_expansion, mul_assoc]

def wordMatrix368 : QuotientMatrix := quotientDecode #v[3012, 12, 1074, 551, 1626, 3254, 3104, 3740, 1437, 2978, 524, 2075]

private theorem wordMatrix368_product : wordMatrix368 = wordMatrix006 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix368_expansion : wordMatrix368 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))) := by
  simp only [wordMatrix368_product, wordMatrix006_expansion, mul_assoc]

def wordMatrix369 : QuotientMatrix := quotientDecode #v[3102, 3846, 2181, 3294, 716, 1706, 2758, 1690, 1180, 197, 1903, 583]

private theorem wordMatrix369_product : wordMatrix369 = wordMatrix367 * wordMatrix368 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix369_expansion : wordMatrix369 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix369_product, wordMatrix367_expansion, wordMatrix368_expansion, mul_assoc]

def wordMatrix370 : QuotientMatrix := quotientDecode #v[1647, 3984, 934, 3545, 309, 1891, 2395, 4049, 2011, 788, 1660, 518]

private theorem wordMatrix370_product : wordMatrix370 = wordMatrix286 * wordMatrix051 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix370_expansion : wordMatrix370 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix370_product, wordMatrix286_expansion, wordMatrix051_expansion, mul_assoc]

def wordMatrix371 : QuotientMatrix := quotientDecode #v[654, 1734, 1772, 3080, 258, 1132, 2042, 3693, 1273, 1627, 2495, 776]

private theorem wordMatrix371_product : wordMatrix371 = wordMatrix370 * wordMatrix041 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix371_expansion : wordMatrix371 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix371_product, wordMatrix370_expansion, wordMatrix041_expansion, mul_assoc]

def wordMatrix372 : QuotientMatrix := quotientDecode #v[2650, 630, 1660, 2343, 3212, 1406, 3129, 1473, 1052, 2557, 374, 1610]

private theorem wordMatrix372_product : wordMatrix372 = wordMatrix147 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix372_expansion : wordMatrix372 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix372_product, wordMatrix147_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix373 : QuotientMatrix := quotientDecode #v[942, 3421, 3848, 3269, 2304, 3702, 2001, 2840, 3826, 3631, 1754, 1048]

private theorem wordMatrix373_product : wordMatrix373 = wordMatrix066 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix373_expansion : wordMatrix373 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix373_product, wordMatrix066_expansion, wordMatrix004_expansion, mul_assoc]

def wordMatrix374 : QuotientMatrix := quotientDecode #v[1406, 3293, 2975, 1383, 2583, 1567, 2783, 1871, 3095, 310, 3072, 3772]

private theorem wordMatrix374_product : wordMatrix374 = wordMatrix372 * wordMatrix373 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix374_expansion : wordMatrix374 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix374_product, wordMatrix372_expansion, wordMatrix373_expansion, mul_assoc]

def wordMatrix375 : QuotientMatrix := quotientDecode #v[170, 1557, 2284, 2286, 511, 2649, 1697, 3942, 646, 1026, 3511, 1966]

private theorem wordMatrix375_product : wordMatrix375 = wordMatrix003 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix375_expansion : wordMatrix375 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv)))) := by
  simp only [wordMatrix375_product, wordMatrix003_expansion, mul_assoc]

def wordMatrix376 : QuotientMatrix := quotientDecode #v[1057, 649, 2318, 3482, 3072, 3831, 3369, 2863, 1461, 2009, 2585, 2777]

private theorem wordMatrix376_product : wordMatrix376 = wordMatrix374 * wordMatrix375 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix376_expansion : wordMatrix376 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix376_product, wordMatrix374_expansion, wordMatrix375_expansion, mul_assoc]

def wordMatrix377 : QuotientMatrix := quotientDecode #v[714, 2729, 2125, 1842, 854, 3505, 2915, 3099, 2545, 76, 3625, 1787]

private theorem wordMatrix377_product : wordMatrix377 = wordMatrix027 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix377_expansion : wordMatrix377 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix377_product, wordMatrix027_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix378 : QuotientMatrix := quotientDecode #v[4050, 2112, 927, 2067, 4080, 3065, 819, 2816, 3403, 315, 1202, 2081]

private theorem wordMatrix378_product : wordMatrix378 = wordMatrix190 * wordMatrix377 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix378_expansion : wordMatrix378 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix378_product, wordMatrix190_expansion, wordMatrix377_expansion, mul_assoc]

def wordMatrix379 : QuotientMatrix := quotientDecode #v[2049, 459, 162, 1447, 3535, 3220, 897, 2986, 2323, 357, 3424, 2551]

private theorem wordMatrix379_product : wordMatrix379 = wordMatrix020 * wordMatrix145 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix379_expansion : wordMatrix379 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))) := by
  simp only [wordMatrix379_product, wordMatrix020_expansion, wordMatrix145_expansion, mul_assoc]

def wordMatrix380 : QuotientMatrix := quotientDecode #v[2254, 2678, 732, 3570, 1425, 1367, 231, 385, 616, 1061, 1626, 3426]

private theorem wordMatrix380_product : wordMatrix380 = wordMatrix378 * wordMatrix379 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix380_expansion : wordMatrix380 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix380_product, wordMatrix378_expansion, wordMatrix379_expansion, mul_assoc]

def wordMatrix381 : QuotientMatrix := quotientDecode #v[2838, 3275, 598, 2434, 3263, 4054, 2234, 2094, 1158, 1536, 2027, 1909]

private theorem wordMatrix381_product : wordMatrix381 = wordMatrix085 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix381_expansion : wordMatrix381 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix381_product, wordMatrix085_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix382 : QuotientMatrix := quotientDecode #v[2330, 3038, 2313, 3345, 123, 3107, 3327, 633, 1692, 2296, 3875, 2606]

private theorem wordMatrix382_product : wordMatrix382 = wordMatrix381 * wordMatrix130 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix382_expansion : wordMatrix382 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix382_product, wordMatrix381_expansion, wordMatrix130_expansion, mul_assoc]

def wordMatrix383 : QuotientMatrix := quotientDecode #v[17, 2032, 1674, 4084, 1182, 236, 178, 4036, 1086, 2102, 943, 1711]

private theorem wordMatrix383_product : wordMatrix383 = wordMatrix382 * wordMatrix168 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix383_expansion : wordMatrix383 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix383_product, wordMatrix382_expansion, wordMatrix168_expansion, mul_assoc]

def wordMatrix384 : QuotientMatrix := quotientDecode #v[291, 3739, 2585, 946, 954, 634, 2231, 3707, 2275, 2523, 3003, 1593]

private theorem wordMatrix384_product : wordMatrix384 = wordMatrix074 * wordMatrix077 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix384_expansion : wordMatrix384 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix384_product, wordMatrix074_expansion, wordMatrix077_expansion, mul_assoc]

def wordMatrix385 : QuotientMatrix := quotientDecode #v[1366, 15, 1754, 729, 1528, 3562, 2023, 2927, 3610, 1034, 3094, 1914]

private theorem wordMatrix385_product : wordMatrix385 = wordMatrix384 * wordMatrix166 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix385_expansion : wordMatrix385 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix385_product, wordMatrix384_expansion, wordMatrix166_expansion, mul_assoc]

def wordMatrix386 : QuotientMatrix := quotientDecode #v[3194, 772, 3072, 2247, 1337, 3293, 973, 2625, 2323, 586, 621, 2044]

private theorem wordMatrix386_product : wordMatrix386 = wordMatrix023 * wordMatrix016 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix386_expansion : wordMatrix386 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))) := by
  simp only [wordMatrix386_product, wordMatrix023_expansion, wordMatrix016_expansion, mul_assoc]

def wordMatrix387 : QuotientMatrix := quotientDecode #v[654, 3001, 1873, 2626, 977, 528, 3867, 2060, 2337, 2478, 4012, 2270]

private theorem wordMatrix387_product : wordMatrix387 = wordMatrix385 * wordMatrix386 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix387_expansion : wordMatrix387 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix387_product, wordMatrix385_expansion, wordMatrix386_expansion, mul_assoc]

def wordMatrix388 : QuotientMatrix := quotientDecode #v[2007, 894, 3802, 2098, 2966, 1392, 2188, 4014, 51, 1299, 1867, 1752]

private theorem wordMatrix388_product : wordMatrix388 = wordMatrix024 * wordMatrix027 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix388_expansion : wordMatrix388 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix388_product, wordMatrix024_expansion, wordMatrix027_expansion, mul_assoc]

def wordMatrix389 : QuotientMatrix := quotientDecode #v[2752, 622, 1306, 1526, 1066, 649, 200, 2619, 2310, 3322, 3103, 1999]

private theorem wordMatrix389_product : wordMatrix389 = wordMatrix076 * wordMatrix087 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix389_expansion : wordMatrix389 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix389_product, wordMatrix076_expansion, wordMatrix087_expansion, mul_assoc]

def wordMatrix390 : QuotientMatrix := quotientDecode #v[2702, 277, 3691, 770, 2902, 882, 3352, 1052, 3597, 2461, 1139, 3018]

private theorem wordMatrix390_product : wordMatrix390 = wordMatrix388 * wordMatrix389 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix390_expansion : wordMatrix390 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix390_product, wordMatrix388_expansion, wordMatrix389_expansion, mul_assoc]

def wordMatrix391 : QuotientMatrix := quotientDecode #v[1813, 3389, 1175, 197, 2887, 1844, 153, 467, 1843, 391, 1241, 1956]

private theorem wordMatrix391_product : wordMatrix391 = wordMatrix096 * wordMatrix081 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix391_expansion : wordMatrix391 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX)))))))))) := by
  simp only [wordMatrix391_product, wordMatrix096_expansion, wordMatrix081_expansion, mul_assoc]

def wordMatrix392 : QuotientMatrix := quotientDecode #v[3743, 4086, 4026, 2953, 868, 1891, 4044, 3020, 445, 2372, 539, 3490]

private theorem wordMatrix392_product : wordMatrix392 = wordMatrix390 * wordMatrix391 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix392_expansion : wordMatrix392 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix392_product, wordMatrix390_expansion, wordMatrix391_expansion, mul_assoc]

def wordMatrix393 : QuotientMatrix := quotientDecode #v[1319, 968, 2579, 1849, 1821, 2080, 4032, 3482, 2576, 2506, 2417, 1406]

private theorem wordMatrix393_product : wordMatrix393 = wordMatrix057 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix393_expansion : wordMatrix393 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix393_product, wordMatrix057_expansion, wordMatrix004_expansion, mul_assoc]

def wordMatrix394 : QuotientMatrix := quotientDecode #v[3240, 2807, 107, 2762, 142, 3180, 2050, 2725, 116, 1128, 2444, 3846]

private theorem wordMatrix394_product : wordMatrix394 = wordMatrix066 * wordMatrix009 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix394_expansion : wordMatrix394 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix394_product, wordMatrix066_expansion, wordMatrix009_expansion, mul_assoc]

def wordMatrix395 : QuotientMatrix := quotientDecode #v[928, 3185, 3519, 1808, 2839, 874, 49, 3304, 3040, 3560, 1850, 3406]

private theorem wordMatrix395_product : wordMatrix395 = wordMatrix393 * wordMatrix394 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix395_expansion : wordMatrix395 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix395_product, wordMatrix393_expansion, wordMatrix394_expansion, mul_assoc]

def wordMatrix396 : QuotientMatrix := quotientDecode #v[170, 220, 876, 4000, 2942, 2765, 960, 1574, 3099, 3734, 2814, 1298]

private theorem wordMatrix396_product : wordMatrix396 = wordMatrix395 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix396_expansion : wordMatrix396 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix396_product, wordMatrix395_expansion, mul_assoc]

def wordMatrix397 : QuotientMatrix := quotientDecode #v[4088, 2909, 3481, 66, 3266, 4030, 1088, 3008, 1157, 1434, 3993, 146]

private theorem wordMatrix397_product : wordMatrix397 = wordMatrix101 * wordMatrix085 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix397_expansion : wordMatrix397 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix397_product, wordMatrix101_expansion, wordMatrix085_expansion, mul_assoc]

def wordMatrix398 : QuotientMatrix := quotientDecode #v[983, 748, 140, 3910, 4085, 994, 3483, 3382, 1104, 4003, 831, 684]

private theorem wordMatrix398_product : wordMatrix398 = wordMatrix024 * wordMatrix077 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix398_expansion : wordMatrix398 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix398_product, wordMatrix024_expansion, wordMatrix077_expansion, mul_assoc]

def wordMatrix399 : QuotientMatrix := quotientDecode #v[2460, 1836, 2961, 3959, 978, 1639, 3748, 2546, 3410, 2054, 1074, 47]

private theorem wordMatrix399_product : wordMatrix399 = wordMatrix397 * wordMatrix398 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix399_expansion : wordMatrix399 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix399_product, wordMatrix397_expansion, wordMatrix398_expansion, mul_assoc]

def wordMatrix400 : QuotientMatrix := quotientDecode #v[1547, 4032, 1683, 458, 1852, 1798, 271, 1458, 2550, 1553, 666, 1787]

private theorem wordMatrix400_product : wordMatrix400 = wordMatrix399 * wordMatrix168 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix400_expansion : wordMatrix400 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix400_product, wordMatrix399_expansion, wordMatrix168_expansion, mul_assoc]

def wordMatrix401 : QuotientMatrix := quotientDecode #v[3292, 3230, 3860, 809, 237, 2100, 3508, 3986, 669, 4021, 2487, 1983]

private theorem wordMatrix401_product : wordMatrix401 = wordMatrix147 * wordMatrix066 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix401_expansion : wordMatrix401 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix401_product, wordMatrix147_expansion, wordMatrix066_expansion, mul_assoc]

def wordMatrix402 : QuotientMatrix := quotientDecode #v[1347, 3280, 1268, 1699, 2553, 46, 61, 2987, 229, 1902, 629, 3866]

private theorem wordMatrix402_product : wordMatrix402 = wordMatrix068 * wordMatrix147 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix402_expansion : wordMatrix402 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix402_product, wordMatrix068_expansion, wordMatrix147_expansion, mul_assoc]

def wordMatrix403 : QuotientMatrix := quotientDecode #v[3415, 442, 2025, 1093, 3244, 569, 2818, 1126, 552, 2351, 228, 3142]

private theorem wordMatrix403_product : wordMatrix403 = wordMatrix401 * wordMatrix402 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix403_expansion : wordMatrix403 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix403_product, wordMatrix401_expansion, wordMatrix402_expansion, mul_assoc]

def wordMatrix404 : QuotientMatrix := quotientDecode #v[3070, 4090, 764, 2109, 2299, 3825, 414, 172, 247, 2748, 2859, 3839]

private theorem wordMatrix404_product : wordMatrix404 = wordMatrix007 * wordMatrix002 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix404_expansion : wordMatrix404 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))) := by
  simp only [wordMatrix404_product, wordMatrix007_expansion, wordMatrix002_expansion, mul_assoc]

def wordMatrix405 : QuotientMatrix := quotientDecode #v[2750, 406, 3424, 951, 328, 3957, 2894, 2370, 3184, 3644, 3391, 2380]

private theorem wordMatrix405_product : wordMatrix405 = wordMatrix403 * wordMatrix404 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix405_expansion : wordMatrix405 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix405_product, wordMatrix403_expansion, wordMatrix404_expansion, mul_assoc]

def wordMatrix406 : QuotientMatrix := quotientDecode #v[3012, 47, 2660, 523, 1306, 37, 3270, 2613, 2344, 2372, 2998, 1134]

private theorem wordMatrix406_product : wordMatrix406 = wordMatrix076 * wordMatrix021 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix406_expansion : wordMatrix406 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix406_product, wordMatrix076_expansion, wordMatrix021_expansion, mul_assoc]

def wordMatrix407 : QuotientMatrix := quotientDecode #v[1065, 2733, 1160, 1602, 3929, 183, 138, 1221, 1461, 2933, 3627, 3038]

private theorem wordMatrix407_product : wordMatrix407 = wordMatrix128 * wordMatrix096 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix407_expansion : wordMatrix407 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix407_product, wordMatrix128_expansion, wordMatrix096_expansion, mul_assoc]

def wordMatrix408 : QuotientMatrix := quotientDecode #v[1497, 3321, 1054, 947, 2088, 22, 3999, 4068, 2206, 2665, 16, 1649]

private theorem wordMatrix408_product : wordMatrix408 = wordMatrix406 * wordMatrix407 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix408_expansion : wordMatrix408 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix408_product, wordMatrix406_expansion, wordMatrix407_expansion, mul_assoc]

def wordMatrix409 : QuotientMatrix := quotientDecode #v[3549, 4002, 2663, 1827, 3864, 1012, 958, 3981, 3405, 2575, 2623, 1946]

private theorem wordMatrix409_product : wordMatrix409 = wordMatrix408 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix409_expansion : wordMatrix409 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix409_product, wordMatrix408_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix410 : QuotientMatrix := quotientDecode #v[2664, 4033, 3636, 1964, 2819, 3385, 939, 3159, 746, 4083, 1634, 3327]

private theorem wordMatrix410_product : wordMatrix410 = wordMatrix076 * wordMatrix101 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix410_expansion : wordMatrix410 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix410_product, wordMatrix076_expansion, wordMatrix101_expansion, mul_assoc]

def wordMatrix411 : QuotientMatrix := quotientDecode #v[338, 2667, 3785, 3467, 1405, 1776, 2202, 491, 1489, 3261, 3853, 3007]

private theorem wordMatrix411_product : wordMatrix411 = wordMatrix074 * wordMatrix238 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix411_expansion : wordMatrix411 = matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix411_product, wordMatrix074_expansion, wordMatrix238_expansion, mul_assoc]

def wordMatrix412 : QuotientMatrix := quotientDecode #v[1251, 1533, 1355, 568, 2538, 3639, 2245, 3237, 1244, 3099, 1969, 1589]

private theorem wordMatrix412_product : wordMatrix412 = wordMatrix410 * wordMatrix411 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix412_expansion : wordMatrix412 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix412_product, wordMatrix410_expansion, wordMatrix411_expansion, mul_assoc]

def wordMatrix413 : QuotientMatrix := quotientDecode #v[318, 1583, 974, 1342, 2867, 178, 1874, 3470, 2911, 344, 9, 1671]

private theorem wordMatrix413_product : wordMatrix413 = wordMatrix017 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix413_expansion : wordMatrix413 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))) := by
  simp only [wordMatrix413_product, wordMatrix017_expansion, mul_assoc]

def wordMatrix414 : QuotientMatrix := quotientDecode #v[3446, 3525, 3627, 4071, 1191, 2184, 3755, 2370, 1814, 3986, 3391, 2080]

private theorem wordMatrix414_product : wordMatrix414 = wordMatrix412 * wordMatrix413 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix414_expansion : wordMatrix414 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix414_product, wordMatrix412_expansion, wordMatrix413_expansion, mul_assoc]

def wordMatrix415 : QuotientMatrix := quotientDecode #v[1892, 1143, 1280, 276, 1677, 578, 469, 3085, 3942, 1181, 1634, 962]

private theorem wordMatrix415_product : wordMatrix415 = wordMatrix350 * wordMatrix061 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix415_expansion : wordMatrix415 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix415_product, wordMatrix350_expansion, wordMatrix061_expansion, mul_assoc]

def wordMatrix416 : QuotientMatrix := quotientDecode #v[3213, 3590, 2714, 3734, 558, 2149, 11, 159, 3040, 1504, 1792, 2641]

private theorem wordMatrix416_product : wordMatrix416 = wordMatrix415 * wordMatrix002 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix416_expansion : wordMatrix416 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix416_product, wordMatrix415_expansion, wordMatrix002_expansion, mul_assoc]

def wordMatrix417 : QuotientMatrix := quotientDecode #v[2080, 1925, 3440, 2881, 2252, 3969, 1623, 3989, 1135, 2098, 2495, 339]

private theorem wordMatrix417_product : wordMatrix417 = wordMatrix244 * wordMatrix078 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix417_expansion : wordMatrix417 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix417_product, wordMatrix244_expansion, wordMatrix078_expansion, mul_assoc]

def wordMatrix418 : QuotientMatrix := quotientDecode #v[1589, 1392, 258, 2796, 2731, 57, 2543, 2244, 1544, 2857, 2614, 47]

private theorem wordMatrix418_product : wordMatrix418 = wordMatrix417 * wordMatrix413 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix418_expansion : wordMatrix418 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix418_product, wordMatrix417_expansion, wordMatrix413_expansion, mul_assoc]

def wordMatrix419 : QuotientMatrix := quotientDecode #v[2825, 3339, 3807, 366, 3624, 1984, 2587, 3168, 2993, 1704, 3954, 2463]

private theorem wordMatrix419_product : wordMatrix419 = wordMatrix030 * wordMatrix008 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix419_expansion : wordMatrix419 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))) := by
  simp only [wordMatrix419_product, wordMatrix030_expansion, wordMatrix008_expansion, mul_assoc]

def wordMatrix420 : QuotientMatrix := quotientDecode #v[1167, 412, 3963, 3760, 644, 308, 1170, 2370, 4021, 3386, 730, 2682]

private theorem wordMatrix420_product : wordMatrix420 = wordMatrix328 * wordMatrix419 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix420_expansion : wordMatrix420 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))) := by
  simp only [wordMatrix420_product, wordMatrix328_expansion, wordMatrix419_expansion, mul_assoc]

def wordMatrix421 : QuotientMatrix := quotientDecode #v[928, 3088, 2845, 3622, 2771, 1911, 1281, 3671, 2536, 2002, 2819, 1159]

private theorem wordMatrix421_product : wordMatrix421 = wordMatrix085 * wordMatrix080 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix421_expansion : wordMatrix421 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix421_product, wordMatrix085_expansion, wordMatrix080_expansion, mul_assoc]

def wordMatrix422 : QuotientMatrix := quotientDecode #v[2007, 498, 1528, 2087, 3860, 1351, 1276, 2359, 1403, 2541, 1051, 4088]

private theorem wordMatrix422_product : wordMatrix422 = wordMatrix027 * wordMatrix080 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix422_expansion : wordMatrix422 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix422_product, wordMatrix027_expansion, wordMatrix080_expansion, mul_assoc]

def wordMatrix423 : QuotientMatrix := quotientDecode #v[230, 1271, 1650, 835, 751, 1535, 1719, 2619, 2600, 2976, 1355, 3825]

private theorem wordMatrix423_product : wordMatrix423 = wordMatrix421 * wordMatrix422 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix423_expansion : wordMatrix423 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix423_product, wordMatrix421_expansion, wordMatrix422_expansion, mul_assoc]

def wordMatrix424 : QuotientMatrix := quotientDecode #v[3824, 2573, 2583, 1373, 1182, 800, 338, 1117, 20, 1449, 1765, 630]

private theorem wordMatrix424_product : wordMatrix424 = wordMatrix017 * wordMatrix016 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix424_expansion : wordMatrix424 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))) := by
  simp only [wordMatrix424_product, wordMatrix017_expansion, wordMatrix016_expansion, mul_assoc]

def wordMatrix425 : QuotientMatrix := quotientDecode #v[1589, 2750, 4013, 18, 2097, 4087, 3653, 449, 418, 182, 1539, 3451]

private theorem wordMatrix425_product : wordMatrix425 = wordMatrix423 * wordMatrix424 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix425_expansion : wordMatrix425 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix425_product, wordMatrix423_expansion, wordMatrix424_expansion, mul_assoc]

def wordMatrix426 : QuotientMatrix := quotientDecode #v[3676, 3801, 3850, 3871, 2939, 2621, 1963, 1277, 1522, 3716, 1629, 47]

private theorem wordMatrix426_product : wordMatrix426 = wordMatrix406 * wordMatrix129 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix426_expansion : wordMatrix426 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix426_product, wordMatrix406_expansion, wordMatrix129_expansion, mul_assoc]

def wordMatrix427 : QuotientMatrix := quotientDecode #v[2592, 3666, 2858, 645, 1103, 942, 824, 294, 2693, 1374, 3348, 1460]

private theorem wordMatrix427_product : wordMatrix427 = wordMatrix426 * wordMatrix023 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix427_expansion : wordMatrix427 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix427_product, wordMatrix426_expansion, wordMatrix023_expansion, mul_assoc]

def wordMatrix428 : QuotientMatrix := quotientDecode #v[970, 163, 670, 3872, 3223, 3181, 1082, 1162, 1631, 3941, 2503, 3091]

private theorem wordMatrix428_product : wordMatrix428 = wordMatrix021 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix428_expansion : wordMatrix428 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix428_product, wordMatrix021_expansion, wordMatrix019_expansion, mul_assoc]

def wordMatrix429 : QuotientMatrix := quotientDecode #v[3748, 3065, 162, 3520, 25, 1459, 225, 909, 3716, 2916, 3893, 642]

private theorem wordMatrix429_product : wordMatrix429 = wordMatrix077 * wordMatrix077 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix429_expansion : wordMatrix429 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix429_product, wordMatrix077_expansion, mul_assoc]

def wordMatrix430 : QuotientMatrix := quotientDecode #v[181, 867, 3691, 3556, 3036, 2851, 3238, 2689, 3222, 771, 2709, 2291]

private theorem wordMatrix430_product : wordMatrix430 = wordMatrix428 * wordMatrix429 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix430_expansion : wordMatrix430 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix430_product, wordMatrix428_expansion, wordMatrix429_expansion, mul_assoc]

def wordMatrix431 : QuotientMatrix := quotientDecode #v[2128, 1533, 3934, 283, 1355, 3267, 863, 453, 2694, 2361, 1506, 1965]

private theorem wordMatrix431_product : wordMatrix431 = wordMatrix430 * wordMatrix081 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix431_expansion : wordMatrix431 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix431_product, wordMatrix430_expansion, wordMatrix081_expansion, mul_assoc]

def wordMatrix432 : QuotientMatrix := quotientDecode #v[1424, 416, 2920, 2279, 1548, 1445, 739, 648, 1333, 108, 70, 3737]

private theorem wordMatrix432_product : wordMatrix432 = wordMatrix019 * wordMatrix087 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix432_expansion : wordMatrix432 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix432_product, wordMatrix019_expansion, wordMatrix087_expansion, mul_assoc]

def wordMatrix433 : QuotientMatrix := quotientDecode #v[2812, 2070, 4085, 1936, 2444, 1509, 2670, 1793, 2083, 486, 246, 2270]

private theorem wordMatrix433_product : wordMatrix433 = wordMatrix432 * wordMatrix175 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix433_expansion : wordMatrix433 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix433_product, wordMatrix432_expansion, wordMatrix175_expansion, mul_assoc]

def wordMatrix434 : QuotientMatrix := quotientDecode #v[3801, 50, 713, 1964, 2970, 1379, 3420, 930, 2338, 2643, 602, 2393]

private theorem wordMatrix434_product : wordMatrix434 = wordMatrix433 * wordMatrix122 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix434_expansion : wordMatrix434 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix434_product, wordMatrix433_expansion, wordMatrix122_expansion, mul_assoc]

def wordMatrix435 : QuotientMatrix := quotientDecode #v[1313, 1426, 3785, 24, 938, 3461, 3107, 292, 3383, 1958, 1200, 305]

private theorem wordMatrix435_product : wordMatrix435 = wordMatrix066 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix435_expansion : wordMatrix435 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix435_product, wordMatrix066_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix436 : QuotientMatrix := quotientDecode #v[3455, 2479, 3078, 563, 3636, 46, 2977, 2870, 1039, 1817, 2930, 380]

private theorem wordMatrix436_product : wordMatrix436 = wordMatrix435 * wordMatrix062 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix436_expansion : wordMatrix436 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix436_product, wordMatrix435_expansion, wordMatrix062_expansion, mul_assoc]

def wordMatrix437 : QuotientMatrix := quotientDecode #v[29, 21, 4027, 1782, 2374, 2489, 3357, 128, 947, 3489, 3954, 2199]

private theorem wordMatrix437_product : wordMatrix437 = wordMatrix436 * wordMatrix008 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix437_expansion : wordMatrix437 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix437_product, wordMatrix436_expansion, wordMatrix008_expansion, mul_assoc]

def wordMatrix438 : QuotientMatrix := quotientDecode #v[157, 505, 3123, 2540, 55, 3197, 1, 198, 1522, 2953, 2503, 3145]

private theorem wordMatrix438_product : wordMatrix438 = wordMatrix004 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix438_expansion : wordMatrix438 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix438_product, wordMatrix004_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix439 : QuotientMatrix := quotientDecode #v[734, 2127, 903, 1893, 1653, 3551, 2699, 1658, 4083, 937, 1735, 1459]

private theorem wordMatrix439_product : wordMatrix439 = wordMatrix052 * wordMatrix043 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix439_expansion : wordMatrix439 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix439_product, wordMatrix052_expansion, wordMatrix043_expansion, mul_assoc]

def wordMatrix440 : QuotientMatrix := quotientDecode #v[1587, 3347, 591, 3980, 700, 1129, 734, 1849, 1568, 2600, 4007, 3140]

private theorem wordMatrix440_product : wordMatrix440 = wordMatrix438 * wordMatrix439 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix440_expansion : wordMatrix440 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix440_product, wordMatrix438_expansion, wordMatrix439_expansion, mul_assoc]

def wordMatrix441 : QuotientMatrix := quotientDecode #v[1550, 3450, 3273, 1436, 328, 83, 2918, 3696, 1221, 2507, 2439, 3204]

private theorem wordMatrix441_product : wordMatrix441 = wordMatrix440 * wordMatrix158 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix441_expansion : wordMatrix441 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix441_product, wordMatrix440_expansion, wordMatrix158_expansion, mul_assoc]

def wordMatrix442 : QuotientMatrix := quotientDecode #v[654, 2504, 3493, 838, 2772, 2360, 2795, 769, 1369, 2370, 1492, 1993]

private theorem wordMatrix442_product : wordMatrix442 = wordMatrix009 * wordMatrix050 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix442_expansion : wordMatrix442 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix442_product, wordMatrix009_expansion, wordMatrix050_expansion, mul_assoc]

def wordMatrix443 : QuotientMatrix := quotientDecode #v[2056, 2376, 376, 669, 2495, 1484, 226, 3309, 3427, 3097, 1781, 349]

private theorem wordMatrix443_product : wordMatrix443 = wordMatrix057 * wordMatrix030 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix443_expansion : wordMatrix443 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix443_product, wordMatrix057_expansion, wordMatrix030_expansion, mul_assoc]

def wordMatrix444 : QuotientMatrix := quotientDecode #v[2649, 684, 2714, 2472, 2444, 720, 1882, 2418, 2142, 1428, 3934, 277]

private theorem wordMatrix444_product : wordMatrix444 = wordMatrix442 * wordMatrix443 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix444_expansion : wordMatrix444 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix444_product, wordMatrix442_expansion, wordMatrix443_expansion, mul_assoc]

def wordMatrix445 : QuotientMatrix := quotientDecode #v[2695, 2834, 3934, 692, 2780, 2126, 240, 1951, 1297, 3611, 23, 1402]

private theorem wordMatrix445_product : wordMatrix445 = wordMatrix444 * wordMatrix006 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix445_expansion : wordMatrix445 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix445_product, wordMatrix444_expansion, wordMatrix006_expansion, mul_assoc]

def wordMatrix446 : QuotientMatrix := quotientDecode #v[60, 2072, 857, 1023, 3143, 1300, 3004, 108, 637, 837, 3651, 2948]

private theorem wordMatrix446_product : wordMatrix446 = wordMatrix057 * wordMatrix045 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix446_expansion : wordMatrix446 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix446_product, wordMatrix057_expansion, wordMatrix045_expansion, mul_assoc]

def wordMatrix447 : QuotientMatrix := quotientDecode #v[635, 3562, 3836, 1858, 1103, 1989, 1088, 1488, 3193, 2976, 3462, 1271]

private theorem wordMatrix447_product : wordMatrix447 = wordMatrix004 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix447_expansion : wordMatrix447 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix447_product, wordMatrix004_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix448 : QuotientMatrix := quotientDecode #v[2612, 2042, 751, 1004, 3164, 2892, 3274, 2619, 1967, 3870, 2304, 2050]

private theorem wordMatrix448_product : wordMatrix448 = wordMatrix446 * wordMatrix447 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix448_expansion : wordMatrix448 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix448_product, wordMatrix446_expansion, wordMatrix447_expansion, mul_assoc]

def wordMatrix449 : QuotientMatrix := quotientDecode #v[3249, 942, 1626, 796, 3744, 3359, 355, 3645, 951, 3211, 2000, 1975]

private theorem wordMatrix449_product : wordMatrix449 = wordMatrix043 * wordMatrix048 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix449_expansion : wordMatrix449 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))) := by
  simp only [wordMatrix449_product, wordMatrix043_expansion, wordMatrix048_expansion, mul_assoc]

def wordMatrix450 : QuotientMatrix := quotientDecode #v[3801, 1215, 1171, 2107, 2786, 3246, 3979, 1152, 407, 1811, 1024, 1049]

private theorem wordMatrix450_product : wordMatrix450 = wordMatrix448 * wordMatrix449 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix450_expansion : wordMatrix450 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY)))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix450_product, wordMatrix448_expansion, wordMatrix449_expansion, mul_assoc]

def wordMatrix451 : QuotientMatrix := quotientDecode #v[3951, 1332, 3041, 1164, 1416, 1978, 919, 4089, 2662, 909, 705, 205]

private theorem wordMatrix451_product : wordMatrix451 = wordMatrix007 * wordMatrix032 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix451_expansion : wordMatrix451 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix451_product, wordMatrix007_expansion, wordMatrix032_expansion, mul_assoc]

def wordMatrix452 : QuotientMatrix := quotientDecode #v[434, 2080, 1551, 2370, 1985, 4023, 3854, 1631, 2343, 774, 4013, 830]

private theorem wordMatrix452_product : wordMatrix452 = wordMatrix362 * wordMatrix451 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix452_expansion : wordMatrix452 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix452_product, wordMatrix362_expansion, wordMatrix451_expansion, mul_assoc]

def wordMatrix453 : QuotientMatrix := quotientDecode #v[2704, 21, 995, 1801, 2417, 3931, 325, 3058, 1382, 1819, 1024, 3701]

private theorem wordMatrix453_product : wordMatrix453 = wordMatrix452 * matrixYInv := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix453_expansion : wordMatrix453 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix453_product, wordMatrix452_expansion, mul_assoc]

def wordMatrix454 : QuotientMatrix := quotientDecode #v[3761, 734, 3535, 3470, 1642, 3115, 13, 562, 3361, 1594, 358, 2389]

private theorem wordMatrix454_product : wordMatrix454 = wordMatrix068 * wordMatrix057 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix454_expansion : wordMatrix454 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix454_product, wordMatrix068_expansion, wordMatrix057_expansion, mul_assoc]

def wordMatrix455 : QuotientMatrix := quotientDecode #v[4094, 3772, 3893, 1164, 974, 3070, 2690, 2309, 1382, 3844, 3313, 2243]

private theorem wordMatrix455_product : wordMatrix455 = wordMatrix258 * wordMatrix454 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix455_expansion : wordMatrix455 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix455_product, wordMatrix258_expansion, wordMatrix454_expansion, mul_assoc]

def wordMatrix456 : QuotientMatrix := quotientDecode #v[862, 1282, 3651, 204, 2942, 1639, 1540, 278, 712, 1133, 1954, 2784]

private theorem wordMatrix456_product : wordMatrix456 = wordMatrix068 * wordMatrix001 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix456_expansion : wordMatrix456 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))) := by
  simp only [wordMatrix456_product, wordMatrix068_expansion, wordMatrix001_expansion, mul_assoc]

def wordMatrix457 : QuotientMatrix := quotientDecode #v[2657, 2991, 3043, 2107, 2618, 3523, 2713, 1333, 3656, 1444, 1047, 2990]

private theorem wordMatrix457_product : wordMatrix457 = wordMatrix455 * wordMatrix456 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix457_expansion : wordMatrix457 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix457_product, wordMatrix455_expansion, wordMatrix456_expansion, mul_assoc]

def wordMatrix458 : QuotientMatrix := quotientDecode #v[259, 3766, 2691, 3516, 2123, 948, 291, 1278, 474, 1033, 3650, 1847]

private theorem wordMatrix458_product : wordMatrix458 = wordMatrix045 * wordMatrix036 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix458_expansion : wordMatrix458 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix458_product, wordMatrix045_expansion, wordMatrix036_expansion, mul_assoc]

def wordMatrix459 : QuotientMatrix := quotientDecode #v[3107, 3559, 1677, 1744, 4073, 2596, 806, 3857, 3051, 1727, 2125, 846]

private theorem wordMatrix459_product : wordMatrix459 = wordMatrix058 * wordMatrix458 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix459_expansion : wordMatrix459 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix459_product, wordMatrix058_expansion, wordMatrix458_expansion, mul_assoc]

def wordMatrix460 : QuotientMatrix := quotientDecode #v[3902, 855, 141, 686, 3948, 114, 425, 1480, 189, 78, 268, 301]

private theorem wordMatrix460_product : wordMatrix460 = wordMatrix459 * matrixY := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix460_expansion : wordMatrix460 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix460_product, wordMatrix459_expansion, mul_assoc]

def wordMatrix461 : QuotientMatrix := quotientDecode #v[2712, 4086, 1985, 2054, 3864, 3700, 443, 1888, 1923, 4000, 539, 2139]

private theorem wordMatrix461_product : wordMatrix461 = wordMatrix021 * wordMatrix080 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix461_expansion : wordMatrix461 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix461_product, wordMatrix021_expansion, wordMatrix080_expansion, mul_assoc]

def wordMatrix462 : QuotientMatrix := quotientDecode #v[3825, 1973, 1268, 394, 1432, 3098, 2431, 3674, 92, 1832, 105, 3895]

private theorem wordMatrix462_product : wordMatrix462 = wordMatrix077 * wordMatrix024 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix462_expansion : wordMatrix462 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix462_product, wordMatrix077_expansion, wordMatrix024_expansion, mul_assoc]

def wordMatrix463 : QuotientMatrix := quotientDecode #v[599, 1484, 3785, 3190, 3128, 3199, 3914, 632, 3, 2666, 2686, 2846]

private theorem wordMatrix463_product : wordMatrix463 = wordMatrix461 * wordMatrix462 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix463_expansion : wordMatrix463 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix463_product, wordMatrix461_expansion, wordMatrix462_expansion, mul_assoc]

def wordMatrix464 : QuotientMatrix := quotientDecode #v[1784, 1851, 2233, 964, 2802, 2549, 3417, 844, 1233, 1602, 268, 2408]

private theorem wordMatrix464_product : wordMatrix464 = wordMatrix463 * wordMatrix023 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix464_expansion : wordMatrix464 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix464_product, wordMatrix463_expansion, wordMatrix023_expansion, mul_assoc]

def wordMatrix465 : QuotientMatrix := quotientDecode #v[1512, 1153, 282, 2643, 904, 2243, 3227, 2798, 2905, 3826, 4046, 1581]

private theorem wordMatrix465_product : wordMatrix465 = wordMatrix080 * wordMatrix073 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix465_expansion : wordMatrix465 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix465_product, wordMatrix080_expansion, wordMatrix073_expansion, mul_assoc]

def wordMatrix466 : QuotientMatrix := quotientDecode #v[3745, 1997, 636, 915, 876, 2707, 1484, 245, 2467, 2082, 2642, 3370]

private theorem wordMatrix466_product : wordMatrix466 = wordMatrix019 * wordMatrix096 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix466_expansion : wordMatrix466 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix466_product, wordMatrix019_expansion, wordMatrix096_expansion, mul_assoc]

def wordMatrix467 : QuotientMatrix := quotientDecode #v[4040, 1030, 3729, 2756, 743, 383, 3614, 3200, 1849, 1105, 1506, 1965]

private theorem wordMatrix467_product : wordMatrix467 = wordMatrix465 * wordMatrix466 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix467_expansion : wordMatrix467 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix467_product, wordMatrix465_expansion, wordMatrix466_expansion, mul_assoc]

def wordMatrix468 : QuotientMatrix := quotientDecode #v[988, 3902, 1810, 1342, 3453, 834, 735, 1834, 1517, 3932, 3838, 3396]

private theorem wordMatrix468_product : wordMatrix468 = wordMatrix467 * wordMatrix015 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix468_expansion : wordMatrix468 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix468_product, wordMatrix467_expansion, wordMatrix015_expansion, mul_assoc]

def wordMatrix469 : QuotientMatrix := quotientDecode #v[2918, 1847, 3283, 3596, 4080, 2667, 2809, 1301, 69, 418, 2439, 1350]

private theorem wordMatrix469_product : wordMatrix469 = wordMatrix043 * wordMatrix030 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix469_expansion : wordMatrix469 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix469_product, wordMatrix043_expansion, wordMatrix030_expansion, mul_assoc]

def wordMatrix470 : QuotientMatrix := quotientDecode #v[377, 412, 9, 3656, 2902, 680, 1070, 2387, 883, 486, 2022, 859]

private theorem wordMatrix470_product : wordMatrix470 = wordMatrix469 * wordMatrix454 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix470_expansion : wordMatrix470 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix470_product, wordMatrix469_expansion, wordMatrix454_expansion, mul_assoc]

def wordMatrix471 : QuotientMatrix := quotientDecode #v[3629, 2194, 2585, 3126, 3043, 4030, 3411, 3720, 2359, 1574, 3841, 2029]

private theorem wordMatrix471_product : wordMatrix471 = wordMatrix036 * wordMatrix000 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix471_expansion : wordMatrix471 = matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))) := by
  simp only [wordMatrix471_product, wordMatrix036_expansion, wordMatrix000_expansion, mul_assoc]

def wordMatrix472 : QuotientMatrix := quotientDecode #v[546, 2675, 539, 4015, 3271, 2854, 3586, 3797, 160, 2009, 3838, 808]

private theorem wordMatrix472_product : wordMatrix472 = wordMatrix470 * wordMatrix471 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix472_expansion : wordMatrix472 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix472_product, wordMatrix470_expansion, wordMatrix471_expansion, mul_assoc]

def wordMatrix473 : QuotientMatrix := quotientDecode #v[3317, 668, 1935, 2643, 2852, 1859, 2866, 883, 3597, 3400, 2714, 3918]

private theorem wordMatrix473_product : wordMatrix473 = wordMatrix009 * wordMatrix012 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix473_expansion : wordMatrix473 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX))))))))))))))) := by
  simp only [wordMatrix473_product, wordMatrix009_expansion, wordMatrix012_expansion, mul_assoc]

def wordMatrix474 : QuotientMatrix := quotientDecode #v[2395, 926, 2172, 1207, 3958, 2135, 89, 2066, 2576, 1033, 1306, 2904]

private theorem wordMatrix474_product : wordMatrix474 = wordMatrix045 * wordMatrix125 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix474_expansion : wordMatrix474 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))) := by
  simp only [wordMatrix474_product, wordMatrix045_expansion, wordMatrix125_expansion, mul_assoc]

def wordMatrix475 : QuotientMatrix := quotientDecode #v[15, 4006, 1311, 2747, 1386, 415, 510, 932, 4059, 188, 3868, 3927]

private theorem wordMatrix475_product : wordMatrix475 = wordMatrix473 * wordMatrix474 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix475_expansion : wordMatrix475 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY)))))))))))))))))))))))))))) := by
  simp only [wordMatrix475_product, wordMatrix473_expansion, wordMatrix474_expansion, mul_assoc]

def wordMatrix476 : QuotientMatrix := quotientDecode #v[372, 3742, 1551, 1087, 1324, 2909, 3798, 2627, 4070, 956, 1051, 126]

private theorem wordMatrix476_product : wordMatrix476 = wordMatrix080 * wordMatrix074 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix476_expansion : wordMatrix476 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix476_product, wordMatrix080_expansion, wordMatrix074_expansion, mul_assoc]

def wordMatrix477 : QuotientMatrix := quotientDecode #v[3407, 3390, 4025, 3643, 3078, 3242, 3927, 3131, 1522, 1342, 2078, 122]

private theorem wordMatrix477_product : wordMatrix477 = wordMatrix476 * wordMatrix025 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix477_expansion : wordMatrix477 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix477_product, wordMatrix476_expansion, wordMatrix025_expansion, mul_assoc]

def wordMatrix478 : QuotientMatrix := quotientDecode #v[4034, 2207, 374, 2224, 3678, 2950, 333, 1817, 1152, 3153, 3531, 4039]

private theorem wordMatrix478_product : wordMatrix478 = wordMatrix096 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix478_expansion : wordMatrix478 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))) := by
  simp only [wordMatrix478_product, wordMatrix096_expansion, mul_assoc]

def wordMatrix479 : QuotientMatrix := quotientDecode #v[2394, 525, 3950, 1128, 3045, 3772, 997, 2105, 600, 3530, 192, 1210]

private theorem wordMatrix479_product : wordMatrix479 = wordMatrix477 * wordMatrix478 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix479_expansion : wordMatrix479 = matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix479_product, wordMatrix477_expansion, wordMatrix478_expansion, mul_assoc]

def wordMatrix480 : QuotientMatrix := quotientDecode #v[1993, 225, 1620, 1477, 112, 642, 3974, 1307, 1690, 1242, 644, 230]

private theorem wordMatrix480_product : wordMatrix480 = wordMatrix087 * wordMatrix019 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix480_expansion : wordMatrix480 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix480_product, wordMatrix087_expansion, wordMatrix019_expansion, mul_assoc]

def wordMatrix481 : QuotientMatrix := quotientDecode #v[2231, 2761, 2091, 3079, 542, 3781, 2072, 1857, 458, 95, 2989, 1768]

private theorem wordMatrix481_product : wordMatrix481 = wordMatrix019 * wordMatrix076 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix481_expansion : wordMatrix481 = matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))) := by
  simp only [wordMatrix481_product, wordMatrix019_expansion, wordMatrix076_expansion, mul_assoc]

def wordMatrix482 : QuotientMatrix := quotientDecode #v[465, 2347, 2527, 1442, 1219, 3543, 2419, 1536, 2147, 36, 3893, 894]

private theorem wordMatrix482_product : wordMatrix482 = wordMatrix480 * wordMatrix481 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix482_expansion : wordMatrix482 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix482_product, wordMatrix480_expansion, wordMatrix481_expansion, mul_assoc]

def wordMatrix483 : QuotientMatrix := quotientDecode #v[1010, 682, 2511, 3814, 1867, 3086, 406, 2984, 727, 3582, 3868, 1839]

private theorem wordMatrix483_product : wordMatrix483 = wordMatrix482 * wordMatrix081 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix483_expansion : wordMatrix483 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix483_product, wordMatrix482_expansion, wordMatrix081_expansion, mul_assoc]

def wordMatrix484 : QuotientMatrix := quotientDecode #v[2607, 2649, 2073, 1478, 1283, 1874, 443, 632, 381, 20, 258, 489]

private theorem wordMatrix484_product : wordMatrix484 = wordMatrix101 * wordMatrix238 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix484_expansion : wordMatrix484 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY))))))))))))))) := by
  simp only [wordMatrix484_product, wordMatrix101_expansion, wordMatrix238_expansion, mul_assoc]

def wordMatrix485 : QuotientMatrix := quotientDecode #v[3089, 1872, 822, 4074, 328, 2812, 3711, 3900, 2039, 2338, 3624, 2128]

private theorem wordMatrix485_product : wordMatrix485 = wordMatrix484 * wordMatrix109 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix485_expansion : wordMatrix485 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix485_product, wordMatrix484_expansion, wordMatrix109_expansion, mul_assoc]

def wordMatrix486 : QuotientMatrix := quotientDecode #v[318, 3886, 2367, 3247, 2417, 2954, 2492, 418, 3410, 2448, 162, 849]

private theorem wordMatrix486_product : wordMatrix486 = wordMatrix101 * matrixX := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix486_expansion : wordMatrix486 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX)))))))) := by
  simp only [wordMatrix486_product, wordMatrix101_expansion, mul_assoc]

def wordMatrix487 : QuotientMatrix := quotientDecode #v[3004, 1197, 40, 1828, 2113, 1460, 2724, 90, 2474, 2727, 3398, 924]

private theorem wordMatrix487_product : wordMatrix487 = wordMatrix485 * wordMatrix486 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix487_expansion : wordMatrix487 = matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX)))))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix487_product, wordMatrix485_expansion, wordMatrix486_expansion, mul_assoc]

def wordMatrix488 : QuotientMatrix := quotientDecode #v[419, 3996, 3750, 2870, 3922, 3793, 1316, 1428, 1630, 812, 2844, 2411]

private theorem wordMatrix488_product : wordMatrix488 = wordMatrix038 * wordMatrix030 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix488_expansion : wordMatrix488 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix488_product, wordMatrix038_expansion, wordMatrix030_expansion, mul_assoc]

def wordMatrix489 : QuotientMatrix := quotientDecode #v[2761, 3822, 1405, 2094, 1173, 3209, 742, 3582, 1113, 2161, 233, 2216]

private theorem wordMatrix489_product : wordMatrix489 = wordMatrix006 * wordMatrix266 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix489_expansion : wordMatrix489 = matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))))) := by
  simp only [wordMatrix489_product, wordMatrix006_expansion, wordMatrix266_expansion, mul_assoc]

def wordMatrix490 : QuotientMatrix := quotientDecode #v[265, 81, 2772, 1807, 3316, 372, 3396, 2214, 3414, 3570, 3398, 3735]

private theorem wordMatrix490_product : wordMatrix490 = wordMatrix488 * wordMatrix489 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix490_expansion : wordMatrix490 = matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv)))))))))))))))))))))) := by
  simp only [wordMatrix490_product, wordMatrix488_expansion, wordMatrix489_expansion, mul_assoc]

def wordMatrix491 : QuotientMatrix := quotientDecode #v[3005, 565, 306, 3656, 978, 3062, 1174, 491, 3529, 686, 2835, 991]

private theorem wordMatrix491_product : wordMatrix491 = wordMatrix045 * wordMatrix004 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix491_expansion : wordMatrix491 = matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))) := by
  simp only [wordMatrix491_product, wordMatrix045_expansion, wordMatrix004_expansion, mul_assoc]

def wordMatrix492 : QuotientMatrix := quotientDecode #v[1790, 1381, 2400, 4071, 158, 185, 3005, 1658, 2486, 2214, 977, 2479]

private theorem wordMatrix492_product : wordMatrix492 = wordMatrix438 * wordMatrix491 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix492_expansion : wordMatrix492 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix492_product, wordMatrix438_expansion, wordMatrix491_expansion, mul_assoc]

def wordMatrix493 : QuotientMatrix := quotientDecode #v[3320, 3904, 2299, 1335, 2233, 1897, 1075, 2597, 3031, 3966, 1650, 3754]

private theorem wordMatrix493_product : wordMatrix493 = wordMatrix002 * wordMatrix000 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix493_expansion : wordMatrix493 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))) := by
  simp only [wordMatrix493_product, wordMatrix002_expansion, wordMatrix000_expansion, mul_assoc]

def wordMatrix494 : QuotientMatrix := quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605]

private theorem wordMatrix494_product : wordMatrix494 = wordMatrix492 * wordMatrix493 := by
  symm
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

theorem wordMatrix494_expansion : wordMatrix494 = matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX * (matrixYInv * (matrixX * (matrixY * (matrixX * (matrixYInv * (matrixX))))))))))))))))))))))))))))))))))))) := by
  simp only [wordMatrix494_product, wordMatrix492_expansion, wordMatrix493_expansion, mul_assoc]


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
