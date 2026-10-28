module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.InnerReps

/-!
# Transitions for the 60-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem innerEdge0_0 : inner0 * hx = hz ^ 0 * inner1 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner0, hMatrixValue_hx, image_power0, image_inner1]
  decide +kernel

public theorem innerEdge0_1 : inner0 * hy = hz ^ 10 * inner1 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner0, hMatrixValue_hy, image_power10, image_inner1]
  decide +kernel

public theorem innerEdge1_0 : inner1 * hx = hz ^ 0 * inner2 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner1, hMatrixValue_hx, image_power0, image_inner2]
  decide +kernel

public theorem innerEdge1_1 : inner1 * hy = hz ^ 0 * inner3 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner1, hMatrixValue_hy, image_power0, image_inner3]
  decide +kernel

public theorem innerEdge2_0 : inner2 * hx = hz ^ 0 * inner4 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner2, hMatrixValue_hx, image_power0, image_inner4]
  decide +kernel

public theorem innerEdge2_1 : inner2 * hy = hz ^ 0 * inner5 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner2, hMatrixValue_hy, image_power0, image_inner5]
  decide +kernel

public theorem innerEdge3_0 : inner3 * hx = hz ^ 0 * inner6 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner3, hMatrixValue_hx, image_power0, image_inner6]
  decide +kernel

public theorem innerEdge3_1 : inner3 * hy = hz ^ 1 * inner0 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner3, hMatrixValue_hy, image_power1, image_inner0]
  decide +kernel

public theorem innerEdge4_0 : inner4 * hx = hz ^ 0 * inner7 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner4, hMatrixValue_hx, image_power0, image_inner7]
  decide +kernel

public theorem innerEdge4_1 : inner4 * hy = hz ^ 0 * inner8 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner4, hMatrixValue_hy, image_power0, image_inner8]
  decide +kernel

public theorem innerEdge5_0 : inner5 * hx = hz ^ 0 * inner9 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner5, hMatrixValue_hx, image_power0, image_inner9]
  decide +kernel

public theorem innerEdge5_1 : inner5 * hy = hz ^ 0 * inner10 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner5, hMatrixValue_hy, image_power0, image_inner10]
  decide +kernel

public theorem innerEdge6_0 : inner6 * hx = hz ^ 0 * inner11 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner6, hMatrixValue_hx, image_power0, image_inner11]
  decide +kernel

public theorem innerEdge6_1 : inner6 * hy = hz ^ 0 * inner12 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner6, hMatrixValue_hy, image_power0, image_inner12]
  decide +kernel

public theorem innerEdge7_0 : inner7 * hx = hz ^ 1 * inner10 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner7, hMatrixValue_hx, image_power1, image_inner10]
  decide +kernel

public theorem innerEdge7_1 : inner7 * hy = hz ^ 10 * inner11 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner7, hMatrixValue_hy, image_power10, image_inner11]
  decide +kernel

public theorem innerEdge8_0 : inner8 * hx = hz ^ 0 * inner13 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner8, hMatrixValue_hx, image_power0, image_inner13]
  decide +kernel

public theorem innerEdge8_1 : inner8 * hy = hz ^ 0 * inner14 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner8, hMatrixValue_hy, image_power0, image_inner14]
  decide +kernel

public theorem innerEdge9_0 : inner9 * hx = hz ^ 10 * inner8 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner9, hMatrixValue_hx, image_power10, image_inner8]
  decide +kernel

public theorem innerEdge9_1 : inner9 * hy = hz ^ 0 * inner15 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner9, hMatrixValue_hy, image_power0, image_inner15]
  decide +kernel

public theorem innerEdge10_0 : inner10 * hx = hz ^ 10 * inner0 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner10, hMatrixValue_hx, image_power10, image_inner0]
  decide +kernel

public theorem innerEdge10_1 : inner10 * hy = hz ^ 0 * inner2 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner10, hMatrixValue_hy, image_power0, image_inner2]
  decide +kernel

public theorem innerEdge11_0 : inner11 * hx = hz ^ 0 * inner16 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner11, hMatrixValue_hx, image_power0, image_inner16]
  decide +kernel

public theorem innerEdge11_1 : inner11 * hy = hz ^ 0 * inner17 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner11, hMatrixValue_hy, image_power0, image_inner17]
  decide +kernel

public theorem innerEdge12_0 : inner12 * hx = hz ^ 0 * inner18 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner12, hMatrixValue_hx, image_power0, image_inner18]
  decide +kernel

public theorem innerEdge12_1 : inner12 * hy = hz ^ 0 * inner19 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner12, hMatrixValue_hy, image_power0, image_inner19]
  decide +kernel

public theorem innerEdge13_0 : inner13 * hx = hz ^ 0 * inner17 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner13, hMatrixValue_hx, image_power0, image_inner17]
  decide +kernel

public theorem innerEdge13_1 : inner13 * hy = hz ^ 0 * inner20 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner13, hMatrixValue_hy, image_power0, image_inner20]
  decide +kernel

public theorem innerEdge14_0 : inner14 * hx = hz ^ 0 * inner21 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner14, hMatrixValue_hx, image_power0, image_inner21]
  decide +kernel

public theorem innerEdge14_1 : inner14 * hy = hz ^ 0 * inner4 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner14, hMatrixValue_hy, image_power0, image_inner4]
  decide +kernel

public theorem innerEdge15_0 : inner15 * hx = hz ^ 0 * inner22 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner15, hMatrixValue_hx, image_power0, image_inner22]
  decide +kernel

public theorem innerEdge15_1 : inner15 * hy = hz ^ 0 * inner23 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner15, hMatrixValue_hy, image_power0, image_inner23]
  decide +kernel

public theorem innerEdge16_0 : inner16 * hx = hz ^ 0 * inner14 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner16, hMatrixValue_hx, image_power0, image_inner14]
  decide +kernel

public theorem innerEdge16_1 : inner16 * hy = hz ^ 6 * inner18 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner16, hMatrixValue_hy, image_power6, image_inner18]
  decide +kernel

public theorem innerEdge17_0 : inner17 * hx = hz ^ 0 * inner24 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner17, hMatrixValue_hx, image_power0, image_inner24]
  decide +kernel

public theorem innerEdge17_1 : inner17 * hy = hz ^ 1 * inner7 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner17, hMatrixValue_hy, image_power1, image_inner7]
  decide +kernel

public theorem innerEdge18_0 : inner18 * hx = hz ^ 0 * inner25 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner18, hMatrixValue_hx, image_power0, image_inner25]
  decide +kernel

public theorem innerEdge18_1 : inner18 * hy = hz ^ 0 * inner26 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner18, hMatrixValue_hy, image_power0, image_inner26]
  decide +kernel

public theorem innerEdge19_0 : inner19 * hx = hz ^ 0 * inner27 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner19, hMatrixValue_hx, image_power0, image_inner27]
  decide +kernel

public theorem innerEdge19_1 : inner19 * hy = hz ^ 0 * inner6 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner19, hMatrixValue_hy, image_power0, image_inner6]
  decide +kernel

public theorem innerEdge20_0 : inner20 * hx = hz ^ 0 * inner28 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner20, hMatrixValue_hx, image_power0, image_inner28]
  decide +kernel

public theorem innerEdge20_1 : inner20 * hy = hz ^ 2 * inner28 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner20, hMatrixValue_hy, image_power2, image_inner28]
  decide +kernel

public theorem innerEdge21_0 : inner21 * hx = hz ^ 0 * inner3 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner21, hMatrixValue_hx, image_power0, image_inner3]
  decide +kernel

public theorem innerEdge21_1 : inner21 * hy = hz ^ 0 * inner29 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner21, hMatrixValue_hy, image_power0, image_inner29]
  decide +kernel

public theorem innerEdge22_0 : inner22 * hx = hz ^ 0 * inner30 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner22, hMatrixValue_hx, image_power0, image_inner30]
  decide +kernel

public theorem innerEdge22_1 : inner22 * hy = hz ^ 1 * inner24 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner22, hMatrixValue_hy, image_power1, image_inner24]
  decide +kernel

public theorem innerEdge23_0 : inner23 * hx = hz ^ 0 * inner31 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner23, hMatrixValue_hx, image_power0, image_inner31]
  decide +kernel

public theorem innerEdge23_1 : inner23 * hy = hz ^ 0 * inner9 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner23, hMatrixValue_hy, image_power0, image_inner9]
  decide +kernel

public theorem innerEdge24_0 : inner24 * hx = hz ^ 1 * inner5 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner24, hMatrixValue_hx, image_power1, image_inner5]
  decide +kernel

public theorem innerEdge24_1 : inner24 * hy = hz ^ 0 * inner32 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner24, hMatrixValue_hy, image_power0, image_inner32]
  decide +kernel

public theorem innerEdge25_0 : inner25 * hx = hz ^ 0 * inner33 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner25, hMatrixValue_hx, image_power0, image_inner33]
  decide +kernel

public theorem innerEdge25_1 : inner25 * hy = hz ^ 6 * inner33 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner25, hMatrixValue_hy, image_power6, image_inner33]
  decide +kernel

public theorem innerEdge26_0 : inner26 * hx = hz ^ 0 * inner34 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner26, hMatrixValue_hx, image_power0, image_inner34]
  decide +kernel

public theorem innerEdge26_1 : inner26 * hy = hz ^ 5 * inner16 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner26, hMatrixValue_hy, image_power5, image_inner16]
  decide +kernel

public theorem innerEdge27_0 : inner27 * hx = hz ^ 0 * inner29 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner27, hMatrixValue_hx, image_power0, image_inner29]
  decide +kernel

public theorem innerEdge27_1 : inner27 * hy = hz ^ 0 * inner35 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner27, hMatrixValue_hy, image_power0, image_inner35]
  decide +kernel

public theorem innerEdge28_0 : inner28 * hx = hz ^ 0 * inner36 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner28, hMatrixValue_hx, image_power0, image_inner36]
  decide +kernel

public theorem innerEdge28_1 : inner28 * hy = hz ^ 9 * inner13 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner28, hMatrixValue_hy, image_power9, image_inner13]
  decide +kernel

public theorem innerEdge29_0 : inner29 * hx = hz ^ 0 * inner37 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner29, hMatrixValue_hx, image_power0, image_inner37]
  decide +kernel

public theorem innerEdge29_1 : inner29 * hy = hz ^ 1 * inner34 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner29, hMatrixValue_hy, image_power1, image_inner34]
  decide +kernel

public theorem innerEdge30_0 : inner30 * hx = hz ^ 1 * inner20 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner30, hMatrixValue_hx, image_power1, image_inner20]
  decide +kernel

public theorem innerEdge30_1 : inner30 * hy = hz ^ 10 * inner36 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner30, hMatrixValue_hy, image_power10, image_inner36]
  decide +kernel

public theorem innerEdge31_0 : inner31 * hx = hz ^ 10 * inner32 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner31, hMatrixValue_hx, image_power10, image_inner32]
  decide +kernel

public theorem innerEdge31_1 : inner31 * hy = hz ^ 0 * inner38 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner31, hMatrixValue_hy, image_power0, image_inner38]
  decide +kernel

public theorem innerEdge32_0 : inner32 * hx = hz ^ 0 * inner39 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner32, hMatrixValue_hx, image_power0, image_inner39]
  decide +kernel

public theorem innerEdge32_1 : inner32 * hy = hz ^ 10 * inner22 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner32, hMatrixValue_hy, image_power10, image_inner22]
  decide +kernel

public theorem innerEdge33_0 : inner33 * hx = hz ^ 6 * inner26 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner33, hMatrixValue_hx, image_power6, image_inner26]
  decide +kernel

public theorem innerEdge33_1 : inner33 * hy = hz ^ 0 * inner40 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner33, hMatrixValue_hy, image_power0, image_inner40]
  decide +kernel

public theorem innerEdge34_0 : inner34 * hx = hz ^ 5 * inner12 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner34, hMatrixValue_hx, image_power5, image_inner12]
  decide +kernel

public theorem innerEdge34_1 : inner34 * hy = hz ^ 10 * inner21 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner34, hMatrixValue_hy, image_power10, image_inner21]
  decide +kernel

public theorem innerEdge35_0 : inner35 * hx = hz ^ 0 * inner41 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner35, hMatrixValue_hx, image_power0, image_inner41]
  decide +kernel

public theorem innerEdge35_1 : inner35 * hy = hz ^ 0 * inner42 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner35, hMatrixValue_hy, image_power0, image_inner42]
  decide +kernel

public theorem innerEdge36_0 : inner36 * hx = hz ^ 10 * inner15 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner36, hMatrixValue_hx, image_power10, image_inner15]
  decide +kernel

public theorem innerEdge36_1 : inner36 * hy = hz ^ 0 * inner43 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner36, hMatrixValue_hy, image_power0, image_inner43]
  decide +kernel

public theorem innerEdge37_0 : inner37 * hx = hz ^ 6 * inner40 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner37, hMatrixValue_hx, image_power6, image_inner40]
  decide +kernel

public theorem innerEdge37_1 : inner37 * hy = hz ^ 0 * inner44 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner37, hMatrixValue_hy, image_power0, image_inner44]
  decide +kernel

public theorem innerEdge38_0 : inner38 * hx = hz ^ 0 * inner45 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner38, hMatrixValue_hx, image_power0, image_inner45]
  decide +kernel

public theorem innerEdge38_1 : inner38 * hy = hz ^ 7 * inner45 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner38, hMatrixValue_hy, image_power7, image_inner45]
  decide +kernel

public theorem innerEdge39_0 : inner39 * hx = hz ^ 0 * inner43 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner39, hMatrixValue_hx, image_power0, image_inner43]
  decide +kernel

public theorem innerEdge39_1 : inner39 * hy = hz ^ 0 * inner46 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner39, hMatrixValue_hy, image_power0, image_inner46]
  decide +kernel

public theorem innerEdge40_0 : inner40 * hx = hz ^ 0 * inner47 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner40, hMatrixValue_hx, image_power0, image_inner47]
  decide +kernel

public theorem innerEdge40_1 : inner40 * hy = hz ^ 5 * inner25 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner40, hMatrixValue_hy, image_power5, image_inner25]
  decide +kernel

public theorem innerEdge41_0 : inner41 * hx = hz ^ 0 * inner48 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner41, hMatrixValue_hx, image_power0, image_inner48]
  decide +kernel

public theorem innerEdge41_1 : inner41 * hy = hz ^ 8 * inner48 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner41, hMatrixValue_hy, image_power8, image_inner48]
  decide +kernel

public theorem innerEdge42_0 : inner42 * hx = hz ^ 0 * inner49 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner42, hMatrixValue_hx, image_power0, image_inner49]
  decide +kernel

public theorem innerEdge42_1 : inner42 * hy = hz ^ 0 * inner27 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner42, hMatrixValue_hy, image_power0, image_inner27]
  decide +kernel

public theorem innerEdge43_0 : inner43 * hx = hz ^ 0 * inner50 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner43, hMatrixValue_hx, image_power0, image_inner50]
  decide +kernel

public theorem innerEdge43_1 : inner43 * hy = hz ^ 1 * inner30 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner43, hMatrixValue_hy, image_power1, image_inner30]
  decide +kernel

public theorem innerEdge44_0 : inner44 * hx = hz ^ 0 * inner51 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner44, hMatrixValue_hx, image_power0, image_inner51]
  decide +kernel

public theorem innerEdge44_1 : inner44 * hy = hz ^ 8 * inner49 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner44, hMatrixValue_hy, image_power8, image_inner49]
  decide +kernel

public theorem innerEdge45_0 : inner45 * hx = hz ^ 0 * inner52 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner45, hMatrixValue_hx, image_power0, image_inner52]
  decide +kernel

public theorem innerEdge45_1 : inner45 * hy = hz ^ 4 * inner31 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner45, hMatrixValue_hy, image_power4, image_inner31]
  decide +kernel

public theorem innerEdge46_0 : inner46 * hx = hz ^ 0 * inner53 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner46, hMatrixValue_hx, image_power0, image_inner53]
  decide +kernel

public theorem innerEdge46_1 : inner46 * hy = hz ^ 0 * inner54 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner46, hMatrixValue_hy, image_power0, image_inner54]
  decide +kernel

public theorem innerEdge47_0 : inner47 * hx = hz ^ 5 * inner19 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner47, hMatrixValue_hx, image_power5, image_inner19]
  decide +kernel

public theorem innerEdge47_1 : inner47 * hy = hz ^ 0 * inner55 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner47, hMatrixValue_hy, image_power0, image_inner55]
  decide +kernel

public theorem innerEdge48_0 : inner48 * hx = hz ^ 8 * inner42 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner48, hMatrixValue_hx, image_power8, image_inner42]
  decide +kernel

public theorem innerEdge48_1 : inner48 * hy = hz ^ 0 * inner56 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner48, hMatrixValue_hy, image_power0, image_inner56]
  decide +kernel

public theorem innerEdge49_0 : inner49 * hx = hz ^ 6 * inner55 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner49, hMatrixValue_hx, image_power6, image_inner55]
  decide +kernel

public theorem innerEdge49_1 : inner49 * hy = hz ^ 3 * inner37 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner49, hMatrixValue_hy, image_power3, image_inner37]
  decide +kernel

public theorem innerEdge50_0 : inner50 * hx = hz ^ 1 * inner23 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner50, hMatrixValue_hx, image_power1, image_inner23]
  decide +kernel

public theorem innerEdge50_1 : inner50 * hy = hz ^ 0 * inner57 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner50, hMatrixValue_hy, image_power0, image_inner57]
  decide +kernel

public theorem innerEdge51_0 : inner51 * hx = hz ^ 0 * inner56 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner51, hMatrixValue_hx, image_power0, image_inner56]
  decide +kernel

public theorem innerEdge51_1 : inner51 * hy = hz ^ 0 * inner50 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner51, hMatrixValue_hy, image_power0, image_inner50]
  decide +kernel

public theorem innerEdge52_0 : inner52 * hx = hz ^ 3 * inner57 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner52, hMatrixValue_hx, image_power3, image_inner57]
  decide +kernel

public theorem innerEdge52_1 : inner52 * hy = hz ^ 0 * inner58 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner52, hMatrixValue_hy, image_power0, image_inner58]
  decide +kernel

public theorem innerEdge53_0 : inner53 * hx = hz ^ 1 * inner58 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner53, hMatrixValue_hx, image_power1, image_inner58]
  decide +kernel

public theorem innerEdge53_1 : inner53 * hy = hz ^ 6 * inner47 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner53, hMatrixValue_hy, image_power6, image_inner47]
  decide +kernel

public theorem innerEdge54_0 : inner54 * hx = hz ^ 0 * inner59 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner54, hMatrixValue_hx, image_power0, image_inner59]
  decide +kernel

public theorem innerEdge54_1 : inner54 * hy = hz ^ 0 * inner39 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner54, hMatrixValue_hy, image_power0, image_inner39]
  decide +kernel

public theorem innerEdge55_0 : inner55 * hx = hz ^ 8 * inner35 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner55, hMatrixValue_hx, image_power8, image_inner35]
  decide +kernel

public theorem innerEdge55_1 : inner55 * hy = hz ^ 5 * inner53 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner55, hMatrixValue_hy, image_power5, image_inner53]
  decide +kernel

public theorem innerEdge56_0 : inner56 * hx = hz ^ 0 * inner46 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner56, hMatrixValue_hx, image_power0, image_inner46]
  decide +kernel

public theorem innerEdge56_1 : inner56 * hy = hz ^ 3 * inner41 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner56, hMatrixValue_hy, image_power3, image_inner41]
  decide +kernel

public theorem innerEdge57_0 : inner57 * hx = hz ^ 7 * inner54 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner57, hMatrixValue_hx, image_power7, image_inner54]
  decide +kernel

public theorem innerEdge57_1 : inner57 * hy = hz ^ 0 * inner51 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner57, hMatrixValue_hy, image_power0, image_inner51]
  decide +kernel

public theorem innerEdge58_0 : inner58 * hx = hz ^ 10 * inner44 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner58, hMatrixValue_hx, image_power10, image_inner44]
  decide +kernel

public theorem innerEdge58_1 : inner58 * hy = hz ^ 6 * inner59 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner58, hMatrixValue_hy, image_power6, image_inner59]
  decide +kernel

public theorem innerEdge59_0 : inner59 * hx = hz ^ 1 * inner38 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner59, hMatrixValue_hx, image_power1, image_inner38]
  decide +kernel

public theorem innerEdge59_1 : inner59 * hy = hz ^ 5 * inner52 := by
  apply hMatrixValue_injective
  simp only [map_mul, image_inner59, hMatrixValue_hy, image_power5, image_inner52]
  decide +kernel


end Janko1.OrderCertificate
