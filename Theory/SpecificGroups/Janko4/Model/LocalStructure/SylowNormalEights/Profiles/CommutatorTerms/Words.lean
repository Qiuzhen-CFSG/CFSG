module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms.Tools

/-!
# Checked literal generator commutators

Each equality uses bounded collection of the defining presentation relations,
with Mathlib's a*b*a⁻¹*b⁻¹ convention. Swapped pairs are reused by inversion.
The certificate generator is `source/generate.py`; its output is checked by
Lean's kernel. The largest certificate uses 410 adjacent rewrites and took
1.29 seconds in kernel checking (2,211,272 KiB peak RSS for the import and probe).

Source: the presentation and candidate words documented in
`SylowNormalEights/source/README.md`.
-/

public section
open scoped commutatorElement
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms

theorem comm_2_128 : ⁅normalForm 2, normalForm 128⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 128 0 3 (by decide +kernel)

theorem comm_2_512 : ⁅normalForm 2, normalForm 512⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 2 512 1572864 5 (by decide +kernel)

theorem comm_2_1024 : ⁅normalForm 2, normalForm 1024⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 1024 0 3 (by decide +kernel)

theorem comm_2_2048 : ⁅normalForm 2, normalForm 2048⁆ = normalForm 2048000 :=
  normalForm_commutator_of_collect 2 2048 2048000 9 (by decide +kernel)

theorem comm_2_4096 : ⁅normalForm 2, normalForm 4096⁆ = normalForm 32768 :=
  normalForm_commutator_of_collect 2 4096 32768 4 (by decide +kernel)

theorem comm_2_8192 : ⁅normalForm 2, normalForm 8192⁆ = normalForm 32768 :=
  normalForm_commutator_of_collect 2 8192 32768 4 (by decide +kernel)

theorem comm_2_16384 : ⁅normalForm 2, normalForm 16384⁆ = normalForm 786432 :=
  normalForm_commutator_of_collect 2 16384 786432 5 (by decide +kernel)

theorem comm_2_32768 : ⁅normalForm 2, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 32768 0 3 (by decide +kernel)

theorem comm_2_32832 : ⁅normalForm 2, normalForm 32832⁆ = normalForm 1917440 :=
  normalForm_commutator_of_collect 2 32832 1917440 19 (by decide +kernel)

theorem comm_2_65536 : ⁅normalForm 2, normalForm 65536⁆ = normalForm 1310720 :=
  normalForm_commutator_of_collect 2 65536 1310720 5 (by decide +kernel)

theorem comm_2_131072 : ⁅normalForm 2, normalForm 131072⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 2 131072 1572864 5 (by decide +kernel)

theorem comm_2_176200 : ⁅normalForm 2, normalForm 176200⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 176200 0 46 (by decide +kernel)

theorem comm_2_262144 : ⁅normalForm 2, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 262144 0 3 (by decide +kernel)

theorem comm_2_524288 : ⁅normalForm 2, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 524288 0 3 (by decide +kernel)

theorem comm_2_606720 : ⁅normalForm 2, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 606720 0 20 (by decide +kernel)

theorem comm_2_1048576 : ⁅normalForm 2, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2 1048576 0 3 (by decide +kernel)

theorem comm_2_1179937 : ⁅normalForm 2, normalForm 1179937⁆ = normalForm 651336 :=
  normalForm_commutator_of_collect 2 1179937 651336 262 (by decide +kernel)

theorem comm_2_1263616 : ⁅normalForm 2, normalForm 1263616⁆ = normalForm 2048000 :=
  normalForm_commutator_of_collect 2 1263616 2048000 44 (by decide +kernel)

theorem comm_2_1312272 : ⁅normalForm 2, normalForm 1312272⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 2 1312272 1572864 23 (by decide +kernel)

theorem comm_4_64 : ⁅normalForm 4, normalForm 64⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4 64 0 4 (by decide +kernel)

theorem comm_4_130 : ⁅normalForm 4, normalForm 130⁆ = normalForm 1066000 :=
  normalForm_commutator_of_collect 4 130 1066000 126 (by decide +kernel)

theorem comm_4_512 : ⁅normalForm 4, normalForm 512⁆ = normalForm 131072 :=
  normalForm_commutator_of_collect 4 512 131072 7 (by decide +kernel)

theorem comm_4_2048 : ⁅normalForm 4, normalForm 2048⁆ = normalForm 1114112 :=
  normalForm_commutator_of_collect 4 2048 1114112 9 (by decide +kernel)

theorem comm_4_8192 : ⁅normalForm 4, normalForm 8192⁆ = normalForm 1376256 :=
  normalForm_commutator_of_collect 4 8192 1376256 17 (by decide +kernel)

theorem comm_4_16384 : ⁅normalForm 4, normalForm 16384⁆ = normalForm 131072 :=
  normalForm_commutator_of_collect 4 16384 131072 7 (by decide +kernel)

theorem comm_4_32768 : ⁅normalForm 4, normalForm 32768⁆ = normalForm 1835008 :=
  normalForm_commutator_of_collect 4 32768 1835008 11 (by decide +kernel)

theorem comm_4_32832 : ⁅normalForm 4, normalForm 32832⁆ = normalForm 1835008 :=
  normalForm_commutator_of_collect 4 32832 1835008 16 (by decide +kernel)

theorem comm_4_65536 : ⁅normalForm 4, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4 65536 0 5 (by decide +kernel)

theorem comm_4_131072 : ⁅normalForm 4, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4 131072 0 5 (by decide +kernel)

theorem comm_4_262144 : ⁅normalForm 4, normalForm 262144⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 4 262144 1572864 9 (by decide +kernel)

theorem comm_4_344576 : ⁅normalForm 4, normalForm 344576⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 4 344576 1572864 26 (by decide +kernel)

theorem comm_4_524288 : ⁅normalForm 4, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4 524288 0 5 (by decide +kernel)

theorem comm_4_664576 : ⁅normalForm 4, normalForm 664576⁆ = normalForm 573440 :=
  normalForm_commutator_of_collect 4 664576 573440 56 (by decide +kernel)

theorem comm_4_804864 : ⁅normalForm 4, normalForm 804864⁆ = normalForm 720896 :=
  normalForm_commutator_of_collect 4 804864 720896 28 (by decide +kernel)

theorem comm_4_1048576 : ⁅normalForm 4, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4 1048576 0 5 (by decide +kernel)

theorem comm_4_1105480 : ⁅normalForm 4, normalForm 1105480⁆ = normalForm 835648 :=
  normalForm_commutator_of_collect 4 1105480 835648 198 (by decide +kernel)

theorem comm_4_1198080 : ⁅normalForm 4, normalForm 1198080⁆ = normalForm 1245184 :=
  normalForm_commutator_of_collect 4 1198080 1245184 24 (by decide +kernel)

theorem comm_4_1319936 : ⁅normalForm 4, normalForm 1319936⁆ = normalForm 1097728 :=
  normalForm_commutator_of_collect 4 1319936 1097728 53 (by decide +kernel)

theorem comm_4_1377808 : ⁅normalForm 4, normalForm 1377808⁆ = normalForm 1917440 :=
  normalForm_commutator_of_collect 4 1377808 1917440 74 (by decide +kernel)

theorem comm_4_1765409 : ⁅normalForm 4, normalForm 1765409⁆ = normalForm 165952 :=
  normalForm_commutator_of_collect 4 1765409 165952 260 (by decide +kernel)

theorem comm_4_1777920 : ⁅normalForm 4, normalForm 1777920⁆ = normalForm 1525760 :=
  normalForm_commutator_of_collect 4 1777920 1525760 73 (by decide +kernel)

theorem comm_33_64 : ⁅normalForm 33, normalForm 64⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 64 1048576 20 (by decide +kernel)

theorem comm_33_130 : ⁅normalForm 33, normalForm 130⁆ = normalForm 1744456 :=
  normalForm_commutator_of_collect 33 130 1744456 211 (by decide +kernel)

theorem comm_33_132 : ⁅normalForm 33, normalForm 132⁆ = normalForm 870976 :=
  normalForm_commutator_of_collect 33 132 870976 166 (by decide +kernel)

theorem comm_33_512 : ⁅normalForm 33, normalForm 512⁆ = normalForm 917504 :=
  normalForm_commutator_of_collect 33 512 917504 23 (by decide +kernel)

theorem comm_33_2048 : ⁅normalForm 33, normalForm 2048⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 33 2048 0 9 (by decide +kernel)

theorem comm_33_8192 : ⁅normalForm 33, normalForm 8192⁆ = normalForm 983040 :=
  normalForm_commutator_of_collect 33 8192 983040 20 (by decide +kernel)

theorem comm_33_16384 : ⁅normalForm 33, normalForm 16384⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 16384 1048576 9 (by decide +kernel)

theorem comm_33_32768 : ⁅normalForm 33, normalForm 32768⁆ = normalForm 1900544 :=
  normalForm_commutator_of_collect 33 32768 1900544 15 (by decide +kernel)

theorem comm_33_65536 : ⁅normalForm 33, normalForm 65536⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 65536 1048576 9 (by decide +kernel)

theorem comm_33_67584 : ⁅normalForm 33, normalForm 67584⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 67584 1048576 18 (by decide +kernel)

theorem comm_33_131072 : ⁅normalForm 33, normalForm 131072⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 131072 1048576 9 (by decide +kernel)

theorem comm_33_262144 : ⁅normalForm 33, normalForm 262144⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 262144 1048576 10 (by decide +kernel)

theorem comm_33_344576 : ⁅normalForm 33, normalForm 344576⁆ = normalForm 1966080 :=
  normalForm_commutator_of_collect 33 344576 1966080 42 (by decide +kernel)

theorem comm_33_524288 : ⁅normalForm 33, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 33 524288 0 9 (by decide +kernel)

theorem comm_33_525312 : ⁅normalForm 33, normalForm 525312⁆ = normalForm 215040 :=
  normalForm_commutator_of_collect 33 525312 215040 27 (by decide +kernel)

theorem comm_33_606720 : ⁅normalForm 33, normalForm 606720⁆ = normalForm 917504 :=
  normalForm_commutator_of_collect 33 606720 917504 40 (by decide +kernel)

theorem comm_33_1048576 : ⁅normalForm 33, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 33 1048576 0 7 (by decide +kernel)

theorem comm_33_1090560 : ⁅normalForm 33, normalForm 1090560⁆ = normalForm 1132544 :=
  normalForm_commutator_of_collect 33 1090560 1132544 52 (by decide +kernel)

theorem comm_33_1105480 : ⁅normalForm 33, normalForm 1105480⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 33 1105480 671744 143 (by decide +kernel)

theorem comm_33_1263616 : ⁅normalForm 33, normalForm 1263616⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 1263616 1048576 30 (by decide +kernel)

theorem comm_33_1312272 : ⁅normalForm 33, normalForm 1312272⁆ = normalForm 1638464 :=
  normalForm_commutator_of_collect 33 1312272 1638464 114 (by decide +kernel)

theorem comm_33_1376320 : ⁅normalForm 33, normalForm 1376320⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 33 1376320 1048576 35 (by decide +kernel)

theorem comm_33_1489992 : ⁅normalForm 33, normalForm 1489992⁆ = normalForm 1785856 :=
  normalForm_commutator_of_collect 33 1489992 1785856 170 (by decide +kernel)

theorem comm_33_1634560 : ⁅normalForm 33, normalForm 1634560⁆ = normalForm 1116160 :=
  normalForm_commutator_of_collect 33 1634560 1116160 76 (by decide +kernel)

theorem comm_33_1638464 : ⁅normalForm 33, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 33 1638464 0 34 (by decide +kernel)

theorem comm_33_1639952 : ⁅normalForm 33, normalForm 1639952⁆ = normalForm 1638464 :=
  normalForm_commutator_of_collect 33 1639952 1638464 128 (by decide +kernel)

theorem comm_64_130 : ⁅normalForm 64, normalForm 130⁆ = normalForm 344576 :=
  normalForm_commutator_of_collect 64 130 344576 57 (by decide +kernel)

theorem comm_64_132 : ⁅normalForm 64, normalForm 132⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 64 132 1572864 12 (by decide +kernel)

theorem comm_64_512 : ⁅normalForm 64, normalForm 512⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 512 0 3 (by decide +kernel)

theorem comm_64_2048 : ⁅normalForm 64, normalForm 2048⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 2048 0 3 (by decide +kernel)

theorem comm_64_8192 : ⁅normalForm 64, normalForm 8192⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 64 8192 1572864 5 (by decide +kernel)

theorem comm_64_16384 : ⁅normalForm 64, normalForm 16384⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 16384 0 3 (by decide +kernel)

theorem comm_64_32768 : ⁅normalForm 64, normalForm 32768⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 64 32768 1572864 5 (by decide +kernel)

theorem comm_64_32832 : ⁅normalForm 64, normalForm 32832⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 64 32832 1572864 8 (by decide +kernel)

theorem comm_64_65536 : ⁅normalForm 64, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 65536 0 3 (by decide +kernel)

theorem comm_64_131072 : ⁅normalForm 64, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 131072 0 3 (by decide +kernel)

theorem comm_64_262144 : ⁅normalForm 64, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 262144 0 3 (by decide +kernel)

theorem comm_64_344576 : ⁅normalForm 64, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 344576 0 9 (by decide +kernel)

theorem comm_64_524288 : ⁅normalForm 64, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 524288 0 3 (by decide +kernel)

theorem comm_64_525312 : ⁅normalForm 64, normalForm 525312⁆ = normalForm 393216 :=
  normalForm_commutator_of_collect 64 525312 393216 7 (by decide +kernel)

theorem comm_64_664576 : ⁅normalForm 64, normalForm 664576⁆ = normalForm 1966080 :=
  normalForm_commutator_of_collect 64 664576 1966080 27 (by decide +kernel)

theorem comm_64_804864 : ⁅normalForm 64, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 804864 0 9 (by decide +kernel)

theorem comm_64_1048576 : ⁅normalForm 64, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 1048576 0 3 (by decide +kernel)

theorem comm_64_1105480 : ⁅normalForm 64, normalForm 1105480⁆ = normalForm 1966080 :=
  normalForm_commutator_of_collect 64 1105480 1966080 97 (by decide +kernel)

theorem comm_64_1198080 : ⁅normalForm 64, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 1198080 0 9 (by decide +kernel)

theorem comm_64_1263616 : ⁅normalForm 64, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 1263616 0 11 (by decide +kernel)

theorem comm_64_1312272 : ⁅normalForm 64, normalForm 1312272⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 64 1312272 1572864 32 (by decide +kernel)

theorem comm_64_1319936 : ⁅normalForm 64, normalForm 1319936⁆ = normalForm 1966080 :=
  normalForm_commutator_of_collect 64 1319936 1966080 23 (by decide +kernel)

theorem comm_64_1376320 : ⁅normalForm 64, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 64 1376320 0 8 (by decide +kernel)

theorem comm_64_1377808 : ⁅normalForm 64, normalForm 1377808⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 64 1377808 1572864 42 (by decide +kernel)

theorem comm_64_1489992 : ⁅normalForm 64, normalForm 1489992⁆ = normalForm 393216 :=
  normalForm_commutator_of_collect 64 1489992 393216 85 (by decide +kernel)

theorem comm_64_1634560 : ⁅normalForm 64, normalForm 1634560⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 64 1634560 1441792 51 (by decide +kernel)

theorem comm_64_1765409 : ⁅normalForm 64, normalForm 1765409⁆ = normalForm 327680 :=
  normalForm_commutator_of_collect 64 1765409 327680 71 (by decide +kernel)

theorem comm_64_1777920 : ⁅normalForm 64, normalForm 1777920⁆ = normalForm 720896 :=
  normalForm_commutator_of_collect 64 1777920 720896 30 (by decide +kernel)

theorem comm_128_512 : ⁅normalForm 128, normalForm 512⁆ = normalForm 786432 :=
  normalForm_commutator_of_collect 128 512 786432 5 (by decide +kernel)

theorem comm_128_1024 : ⁅normalForm 128, normalForm 1024⁆ = normalForm 32768 :=
  normalForm_commutator_of_collect 128 1024 32768 4 (by decide +kernel)

theorem comm_128_2048 : ⁅normalForm 128, normalForm 2048⁆ = normalForm 65536 :=
  normalForm_commutator_of_collect 128 2048 65536 4 (by decide +kernel)

theorem comm_128_4096 : ⁅normalForm 128, normalForm 4096⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 4096 0 3 (by decide +kernel)

theorem comm_128_8192 : ⁅normalForm 128, normalForm 8192⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 8192 0 3 (by decide +kernel)

theorem comm_128_16384 : ⁅normalForm 128, normalForm 16384⁆ = normalForm 786432 :=
  normalForm_commutator_of_collect 128 16384 786432 5 (by decide +kernel)

theorem comm_128_32768 : ⁅normalForm 128, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 32768 0 3 (by decide +kernel)

theorem comm_128_32832 : ⁅normalForm 128, normalForm 32832⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 128 32832 1572864 13 (by decide +kernel)

theorem comm_128_65536 : ⁅normalForm 128, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 65536 0 3 (by decide +kernel)

theorem comm_128_131072 : ⁅normalForm 128, normalForm 131072⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 128 131072 1572864 5 (by decide +kernel)

theorem comm_128_176200 : ⁅normalForm 128, normalForm 176200⁆ = normalForm 1310720 :=
  normalForm_commutator_of_collect 128 176200 1310720 49 (by decide +kernel)

theorem comm_128_262144 : ⁅normalForm 128, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 262144 0 3 (by decide +kernel)

theorem comm_128_524288 : ⁅normalForm 128, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 524288 0 3 (by decide +kernel)

theorem comm_128_606720 : ⁅normalForm 128, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 606720 0 14 (by decide +kernel)

theorem comm_128_1048576 : ⁅normalForm 128, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 128 1048576 0 3 (by decide +kernel)

theorem comm_128_1179937 : ⁅normalForm 128, normalForm 1179937⁆ = normalForm 1884672 :=
  normalForm_commutator_of_collect 128 1179937 1884672 139 (by decide +kernel)

theorem comm_128_1263616 : ⁅normalForm 128, normalForm 1263616⁆ = normalForm 1376256 :=
  normalForm_commutator_of_collect 128 1263616 1376256 27 (by decide +kernel)

theorem comm_128_1312272 : ⁅normalForm 128, normalForm 1312272⁆ = normalForm 786432 :=
  normalForm_commutator_of_collect 128 1312272 786432 29 (by decide +kernel)

theorem comm_130_132 : ⁅normalForm 130, normalForm 132⁆ = normalForm 1066000 :=
  normalForm_commutator_of_collect 130 132 1066000 102 (by decide +kernel)

theorem comm_130_512 : ⁅normalForm 130, normalForm 512⁆ = normalForm 1310720 :=
  normalForm_commutator_of_collect 130 512 1310720 13 (by decide +kernel)

theorem comm_130_2048 : ⁅normalForm 130, normalForm 2048⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 130 2048 671744 18 (by decide +kernel)

theorem comm_130_8192 : ⁅normalForm 130, normalForm 8192⁆ = normalForm 32768 :=
  normalForm_commutator_of_collect 130 8192 32768 6 (by decide +kernel)

theorem comm_130_16384 : ⁅normalForm 130, normalForm 16384⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 16384 0 10 (by decide +kernel)

theorem comm_130_32768 : ⁅normalForm 130, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 32768 0 5 (by decide +kernel)

theorem comm_130_32832 : ⁅normalForm 130, normalForm 32832⁆ = normalForm 344576 :=
  normalForm_commutator_of_collect 130 32832 344576 27 (by decide +kernel)

theorem comm_130_65536 : ⁅normalForm 130, normalForm 65536⁆ = normalForm 1310720 :=
  normalForm_commutator_of_collect 130 65536 1310720 7 (by decide +kernel)

theorem comm_130_67584 : ⁅normalForm 130, normalForm 67584⁆ = normalForm 1982464 :=
  normalForm_commutator_of_collect 130 67584 1982464 17 (by decide +kernel)

theorem comm_130_131072 : ⁅normalForm 130, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 131072 0 10 (by decide +kernel)

theorem comm_130_262144 : ⁅normalForm 130, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 262144 0 5 (by decide +kernel)

theorem comm_130_344576 : ⁅normalForm 130, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 344576 0 30 (by decide +kernel)

theorem comm_130_524288 : ⁅normalForm 130, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 524288 0 5 (by decide +kernel)

theorem comm_130_525312 : ⁅normalForm 130, normalForm 525312⁆ = normalForm 32768 :=
  normalForm_commutator_of_collect 130 525312 32768 10 (by decide +kernel)

theorem comm_130_606720 : ⁅normalForm 130, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 606720 0 30 (by decide +kernel)

theorem comm_130_664576 : ⁅normalForm 130, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 664576 0 20 (by decide +kernel)

theorem comm_130_804864 : ⁅normalForm 130, normalForm 804864⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 130 804864 671744 37 (by decide +kernel)

theorem comm_130_1048576 : ⁅normalForm 130, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 1048576 0 5 (by decide +kernel)

theorem comm_130_1090560 : ⁅normalForm 130, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 1090560 0 15 (by decide +kernel)

theorem comm_130_1105480 : ⁅normalForm 130, normalForm 1105480⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 130 1105480 671744 163 (by decide +kernel)

theorem comm_130_1198080 : ⁅normalForm 130, normalForm 1198080⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 130 1198080 671744 45 (by decide +kernel)

theorem comm_130_1263616 : ⁅normalForm 130, normalForm 1263616⁆ = normalForm 1982464 :=
  normalForm_commutator_of_collect 130 1263616 1982464 53 (by decide +kernel)

theorem comm_130_1312272 : ⁅normalForm 130, normalForm 1312272⁆ = normalForm 1310720 :=
  normalForm_commutator_of_collect 130 1312272 1310720 39 (by decide +kernel)

theorem comm_130_1319936 : ⁅normalForm 130, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 1319936 0 17 (by decide +kernel)

theorem comm_130_1376320 : ⁅normalForm 130, normalForm 1376320⁆ = normalForm 1131008 :=
  normalForm_commutator_of_collect 130 1376320 1131008 33 (by decide +kernel)

theorem comm_130_1377808 : ⁅normalForm 130, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 1377808 0 42 (by decide +kernel)

theorem comm_130_1489992 : ⁅normalForm 130, normalForm 1489992⁆ = normalForm 1753088 :=
  normalForm_commutator_of_collect 130 1489992 1753088 196 (by decide +kernel)

theorem comm_130_1634560 : ⁅normalForm 130, normalForm 1634560⁆ = normalForm 1090560 :=
  normalForm_commutator_of_collect 130 1634560 1090560 51 (by decide +kernel)

theorem comm_130_1638464 : ⁅normalForm 130, normalForm 1638464⁆ = normalForm 1131008 :=
  normalForm_commutator_of_collect 130 1638464 1131008 27 (by decide +kernel)

theorem comm_130_1639952 : ⁅normalForm 130, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 130 1639952 0 42 (by decide +kernel)

theorem comm_130_1765409 : ⁅normalForm 130, normalForm 1765409⁆ = normalForm 1105480 :=
  normalForm_commutator_of_collect 130 1765409 1105480 410 (by decide +kernel)

theorem comm_130_1777920 : ⁅normalForm 130, normalForm 1777920⁆ = normalForm 1319936 :=
  normalForm_commutator_of_collect 130 1777920 1319936 30 (by decide +kernel)

theorem comm_132_512 : ⁅normalForm 132, normalForm 512⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 132 512 1441792 17 (by decide +kernel)

theorem comm_132_2048 : ⁅normalForm 132, normalForm 2048⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 132 2048 1048576 12 (by decide +kernel)

theorem comm_132_8192 : ⁅normalForm 132, normalForm 8192⁆ = normalForm 1376256 :=
  normalForm_commutator_of_collect 132 8192 1376256 19 (by decide +kernel)

theorem comm_132_16384 : ⁅normalForm 132, normalForm 16384⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 132 16384 1441792 17 (by decide +kernel)

theorem comm_132_32768 : ⁅normalForm 132, normalForm 32768⁆ = normalForm 1835008 :=
  normalForm_commutator_of_collect 132 32768 1835008 13 (by decide +kernel)

theorem comm_132_65536 : ⁅normalForm 132, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 132 65536 0 7 (by decide +kernel)

theorem comm_132_67584 : ⁅normalForm 132, normalForm 67584⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 132 67584 1048576 14 (by decide +kernel)

theorem comm_132_131072 : ⁅normalForm 132, normalForm 131072⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 132 131072 1572864 13 (by decide +kernel)

theorem comm_132_262144 : ⁅normalForm 132, normalForm 262144⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 132 262144 1572864 11 (by decide +kernel)

theorem comm_132_344576 : ⁅normalForm 132, normalForm 344576⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 132 344576 1572864 36 (by decide +kernel)

theorem comm_132_524288 : ⁅normalForm 132, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 132 524288 0 7 (by decide +kernel)

theorem comm_132_525312 : ⁅normalForm 132, normalForm 525312⁆ = normalForm 1130496 :=
  normalForm_commutator_of_collect 132 525312 1130496 36 (by decide +kernel)

theorem comm_132_606720 : ⁅normalForm 132, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 132 606720 0 26 (by decide +kernel)

theorem comm_132_1048576 : ⁅normalForm 132, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 132 1048576 0 7 (by decide +kernel)

theorem comm_132_1090560 : ⁅normalForm 132, normalForm 1090560⁆ = normalForm 540672 :=
  normalForm_commutator_of_collect 132 1090560 540672 60 (by decide +kernel)

theorem comm_132_1105480 : ⁅normalForm 132, normalForm 1105480⁆ = normalForm 81984 :=
  normalForm_commutator_of_collect 132 1105480 81984 236 (by decide +kernel)

theorem comm_132_1263616 : ⁅normalForm 132, normalForm 1263616⁆ = normalForm 1966080 :=
  normalForm_commutator_of_collect 132 1263616 1966080 51 (by decide +kernel)

theorem comm_132_1312272 : ⁅normalForm 132, normalForm 1312272⁆ = normalForm 606720 :=
  normalForm_commutator_of_collect 132 1312272 606720 84 (by decide +kernel)

theorem comm_132_1376320 : ⁅normalForm 132, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 132 1376320 0 25 (by decide +kernel)

theorem comm_132_1489992 : ⁅normalForm 132, normalForm 1489992⁆ = normalForm 1851456 :=
  normalForm_commutator_of_collect 132 1489992 1851456 223 (by decide +kernel)

theorem comm_132_1634560 : ⁅normalForm 132, normalForm 1634560⁆ = normalForm 1132544 :=
  normalForm_commutator_of_collect 132 1634560 1132544 93 (by decide +kernel)

theorem comm_132_1638464 : ⁅normalForm 132, normalForm 1638464⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 132 1638464 1572864 20 (by decide +kernel)

theorem comm_132_1639952 : ⁅normalForm 132, normalForm 1639952⁆ = normalForm 1131008 :=
  normalForm_commutator_of_collect 132 1639952 1131008 94 (by decide +kernel)

theorem comm_512_1024 : ⁅normalForm 512, normalForm 1024⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 512 1024 1572864 5 (by decide +kernel)

theorem comm_512_2048 : ⁅normalForm 512, normalForm 2048⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 2048 0 3 (by decide +kernel)

theorem comm_512_4096 : ⁅normalForm 512, normalForm 4096⁆ = normalForm 786432 :=
  normalForm_commutator_of_collect 512 4096 786432 5 (by decide +kernel)

theorem comm_512_8192 : ⁅normalForm 512, normalForm 8192⁆ = normalForm 524288 :=
  normalForm_commutator_of_collect 512 8192 524288 4 (by decide +kernel)

theorem comm_512_16384 : ⁅normalForm 512, normalForm 16384⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 16384 0 3 (by decide +kernel)

theorem comm_512_32768 : ⁅normalForm 512, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 32768 0 3 (by decide +kernel)

theorem comm_512_32832 : ⁅normalForm 512, normalForm 32832⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 32832 0 5 (by decide +kernel)

theorem comm_512_65536 : ⁅normalForm 512, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 65536 0 3 (by decide +kernel)

theorem comm_512_131072 : ⁅normalForm 512, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 131072 0 3 (by decide +kernel)

theorem comm_512_176200 : ⁅normalForm 512, normalForm 176200⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 176200 0 27 (by decide +kernel)

theorem comm_512_262144 : ⁅normalForm 512, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 262144 0 3 (by decide +kernel)

theorem comm_512_344576 : ⁅normalForm 512, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 344576 0 8 (by decide +kernel)

theorem comm_512_524288 : ⁅normalForm 512, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 524288 0 3 (by decide +kernel)

theorem comm_512_525312 : ⁅normalForm 512, normalForm 525312⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 512 525312 1572864 9 (by decide +kernel)

theorem comm_512_606720 : ⁅normalForm 512, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 606720 0 8 (by decide +kernel)

theorem comm_512_664576 : ⁅normalForm 512, normalForm 664576⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 512 664576 1048576 19 (by decide +kernel)

theorem comm_512_1048576 : ⁅normalForm 512, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 1048576 0 3 (by decide +kernel)

theorem comm_512_1105480 : ⁅normalForm 512, normalForm 1105480⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 512 1105480 1048576 51 (by decide +kernel)

theorem comm_512_1179937 : ⁅normalForm 512, normalForm 1179937⁆ = normalForm 1835008 :=
  normalForm_commutator_of_collect 512 1179937 1835008 48 (by decide +kernel)

theorem comm_512_1198080 : ⁅normalForm 512, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 1198080 0 9 (by decide +kernel)

theorem comm_512_1263616 : ⁅normalForm 512, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 1263616 0 11 (by decide +kernel)

theorem comm_512_1312272 : ⁅normalForm 512, normalForm 1312272⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 512 1312272 1572864 20 (by decide +kernel)

theorem comm_512_1376320 : ⁅normalForm 512, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 512 1376320 0 9 (by decide +kernel)

theorem comm_512_1377808 : ⁅normalForm 512, normalForm 1377808⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 512 1377808 1572864 26 (by decide +kernel)

theorem comm_512_1489992 : ⁅normalForm 512, normalForm 1489992⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 512 1489992 1572864 68 (by decide +kernel)

theorem comm_512_1634560 : ⁅normalForm 512, normalForm 1634560⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 512 1634560 1441792 46 (by decide +kernel)

theorem comm_512_1765409 : ⁅normalForm 512, normalForm 1765409⁆ = normalForm 1703936 :=
  normalForm_commutator_of_collect 512 1765409 1703936 82 (by decide +kernel)

theorem comm_512_1777920 : ⁅normalForm 512, normalForm 1777920⁆ = normalForm 655360 :=
  normalForm_commutator_of_collect 512 1777920 655360 22 (by decide +kernel)

theorem comm_1024_2048 : ⁅normalForm 1024, normalForm 2048⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 2048 0 3 (by decide +kernel)

theorem comm_1024_4096 : ⁅normalForm 1024, normalForm 4096⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 4096 0 3 (by decide +kernel)

theorem comm_1024_8192 : ⁅normalForm 1024, normalForm 8192⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 8192 0 3 (by decide +kernel)

theorem comm_1024_16384 : ⁅normalForm 1024, normalForm 16384⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1024 16384 1048576 4 (by decide +kernel)

theorem comm_1024_32768 : ⁅normalForm 1024, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 32768 0 3 (by decide +kernel)

theorem comm_1024_32832 : ⁅normalForm 1024, normalForm 32832⁆ = normalForm 393216 :=
  normalForm_commutator_of_collect 1024 32832 393216 13 (by decide +kernel)

theorem comm_1024_65536 : ⁅normalForm 1024, normalForm 65536⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1024 65536 1048576 4 (by decide +kernel)

theorem comm_1024_131072 : ⁅normalForm 1024, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 131072 0 3 (by decide +kernel)

theorem comm_1024_176200 : ⁅normalForm 1024, normalForm 176200⁆ = normalForm 2048000 :=
  normalForm_commutator_of_collect 1024 176200 2048000 103 (by decide +kernel)

theorem comm_1024_262144 : ⁅normalForm 1024, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 262144 0 3 (by decide +kernel)

theorem comm_1024_524288 : ⁅normalForm 1024, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 524288 0 3 (by decide +kernel)

theorem comm_1024_606720 : ⁅normalForm 1024, normalForm 606720⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 1024 606720 1572864 23 (by decide +kernel)

theorem comm_1024_1048576 : ⁅normalForm 1024, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 1048576 0 3 (by decide +kernel)

theorem comm_1024_1179937 : ⁅normalForm 1024, normalForm 1179937⁆ = normalForm 215040 :=
  normalForm_commutator_of_collect 1024 1179937 215040 57 (by decide +kernel)

theorem comm_1024_1263616 : ⁅normalForm 1024, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1024 1263616 0 13 (by decide +kernel)

theorem comm_1024_1312272 : ⁅normalForm 1024, normalForm 1312272⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 1024 1312272 1572864 22 (by decide +kernel)

theorem comm_2048_4096 : ⁅normalForm 2048, normalForm 4096⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 4096 0 3 (by decide +kernel)

theorem comm_2048_8192 : ⁅normalForm 2048, normalForm 8192⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 8192 0 3 (by decide +kernel)

theorem comm_2048_16384 : ⁅normalForm 2048, normalForm 16384⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 16384 0 3 (by decide +kernel)

theorem comm_2048_32768 : ⁅normalForm 2048, normalForm 32768⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 2048 32768 1048576 4 (by decide +kernel)

theorem comm_2048_32832 : ⁅normalForm 2048, normalForm 32832⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 2048 32832 1048576 7 (by decide +kernel)

theorem comm_2048_65536 : ⁅normalForm 2048, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 65536 0 3 (by decide +kernel)

theorem comm_2048_131072 : ⁅normalForm 2048, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 131072 0 3 (by decide +kernel)

theorem comm_2048_176200 : ⁅normalForm 2048, normalForm 176200⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 176200 0 23 (by decide +kernel)

theorem comm_2048_262144 : ⁅normalForm 2048, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 262144 0 3 (by decide +kernel)

theorem comm_2048_344576 : ⁅normalForm 2048, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 344576 0 9 (by decide +kernel)

theorem comm_2048_524288 : ⁅normalForm 2048, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 524288 0 3 (by decide +kernel)

theorem comm_2048_525312 : ⁅normalForm 2048, normalForm 525312⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 525312 0 5 (by decide +kernel)

theorem comm_2048_606720 : ⁅normalForm 2048, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 606720 0 9 (by decide +kernel)

theorem comm_2048_664576 : ⁅normalForm 2048, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 664576 0 9 (by decide +kernel)

theorem comm_2048_1048576 : ⁅normalForm 2048, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 1048576 0 3 (by decide +kernel)

theorem comm_2048_1105480 : ⁅normalForm 2048, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 1105480 0 27 (by decide +kernel)

theorem comm_2048_1179937 : ⁅normalForm 2048, normalForm 1179937⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 2048 1179937 1048576 19 (by decide +kernel)

theorem comm_2048_1198080 : ⁅normalForm 2048, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 1198080 0 8 (by decide +kernel)

theorem comm_2048_1263616 : ⁅normalForm 2048, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 1263616 0 10 (by decide +kernel)

theorem comm_2048_1312272 : ⁅normalForm 2048, normalForm 1312272⁆ = normalForm 917504 :=
  normalForm_commutator_of_collect 2048 1312272 917504 29 (by decide +kernel)

theorem comm_2048_1376320 : ⁅normalForm 2048, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 1376320 0 9 (by decide +kernel)

theorem comm_2048_1377808 : ⁅normalForm 2048, normalForm 1377808⁆ = normalForm 917504 :=
  normalForm_commutator_of_collect 2048 1377808 917504 37 (by decide +kernel)

theorem comm_2048_1489992 : ⁅normalForm 2048, normalForm 1489992⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 1489992 0 32 (by decide +kernel)

theorem comm_2048_1634560 : ⁅normalForm 2048, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 2048 1634560 0 21 (by decide +kernel)

theorem comm_2048_1765409 : ⁅normalForm 2048, normalForm 1765409⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 2048 1765409 1048576 33 (by decide +kernel)

theorem comm_2048_1777920 : ⁅normalForm 2048, normalForm 1777920⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 2048 1777920 1048576 21 (by decide +kernel)

theorem comm_4096_8192 : ⁅normalForm 4096, normalForm 8192⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4096 8192 0 3 (by decide +kernel)

theorem comm_4096_16384 : ⁅normalForm 4096, normalForm 16384⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4096 16384 0 3 (by decide +kernel)

theorem comm_4096_32768 : ⁅normalForm 4096, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4096 32768 0 3 (by decide +kernel)

theorem comm_4096_32832 : ⁅normalForm 4096, normalForm 32832⁆ = normalForm 1376256 :=
  normalForm_commutator_of_collect 4096 32832 1376256 17 (by decide +kernel)

theorem comm_4096_65536 : ⁅normalForm 4096, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4096 65536 0 3 (by decide +kernel)

theorem comm_4096_131072 : ⁅normalForm 4096, normalForm 131072⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 4096 131072 1048576 4 (by decide +kernel)

theorem comm_4096_176200 : ⁅normalForm 4096, normalForm 176200⁆ = normalForm 1376256 :=
  normalForm_commutator_of_collect 4096 176200 1376256 47 (by decide +kernel)

theorem comm_4096_262144 : ⁅normalForm 4096, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4096 262144 0 3 (by decide +kernel)

theorem comm_4096_524288 : ⁅normalForm 4096, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4096 524288 0 3 (by decide +kernel)

theorem comm_4096_606720 : ⁅normalForm 4096, normalForm 606720⁆ = normalForm 786432 :=
  normalForm_commutator_of_collect 4096 606720 786432 19 (by decide +kernel)

theorem comm_4096_1048576 : ⁅normalForm 4096, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 4096 1048576 0 3 (by decide +kernel)

theorem comm_4096_1179937 : ⁅normalForm 4096, normalForm 1179937⁆ = normalForm 16384 :=
  normalForm_commutator_of_collect 4096 1179937 16384 23 (by decide +kernel)

theorem comm_4096_1263616 : ⁅normalForm 4096, normalForm 1263616⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 4096 1263616 1048576 15 (by decide +kernel)

theorem comm_4096_1312272 : ⁅normalForm 4096, normalForm 1312272⁆ = normalForm 819200 :=
  normalForm_commutator_of_collect 4096 1312272 819200 29 (by decide +kernel)

theorem comm_8192_16384 : ⁅normalForm 8192, normalForm 16384⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 8192 16384 1048576 4 (by decide +kernel)

theorem comm_8192_32768 : ⁅normalForm 8192, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 32768 0 3 (by decide +kernel)

theorem comm_8192_32832 : ⁅normalForm 8192, normalForm 32832⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 8192 32832 1572864 13 (by decide +kernel)

theorem comm_8192_65536 : ⁅normalForm 8192, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 65536 0 3 (by decide +kernel)

theorem comm_8192_67584 : ⁅normalForm 8192, normalForm 67584⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 67584 0 5 (by decide +kernel)

theorem comm_8192_131072 : ⁅normalForm 8192, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 131072 0 3 (by decide +kernel)

theorem comm_8192_176200 : ⁅normalForm 8192, normalForm 176200⁆ = normalForm 1376256 :=
  normalForm_commutator_of_collect 8192 176200 1376256 58 (by decide +kernel)

theorem comm_8192_262144 : ⁅normalForm 8192, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 262144 0 3 (by decide +kernel)

theorem comm_8192_344576 : ⁅normalForm 8192, normalForm 344576⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 8192 344576 1572864 24 (by decide +kernel)

theorem comm_8192_524288 : ⁅normalForm 8192, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 524288 0 3 (by decide +kernel)

theorem comm_8192_525312 : ⁅normalForm 8192, normalForm 525312⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 525312 0 5 (by decide +kernel)

theorem comm_8192_606720 : ⁅normalForm 8192, normalForm 606720⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 8192 606720 1572864 18 (by decide +kernel)

theorem comm_8192_664576 : ⁅normalForm 8192, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 664576 0 8 (by decide +kernel)

theorem comm_8192_804864 : ⁅normalForm 8192, normalForm 804864⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 8192 804864 1048576 15 (by decide +kernel)

theorem comm_8192_1048576 : ⁅normalForm 8192, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 1048576 0 3 (by decide +kernel)

theorem comm_8192_1090560 : ⁅normalForm 8192, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 1090560 0 8 (by decide +kernel)

theorem comm_8192_1105480 : ⁅normalForm 8192, normalForm 1105480⁆ = normalForm 851968 :=
  normalForm_commutator_of_collect 8192 1105480 851968 98 (by decide +kernel)

theorem comm_8192_1179937 : ⁅normalForm 8192, normalForm 1179937⁆ = normalForm 983040 :=
  normalForm_commutator_of_collect 8192 1179937 983040 56 (by decide +kernel)

theorem comm_8192_1198080 : ⁅normalForm 8192, normalForm 1198080⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 8192 1198080 1048576 13 (by decide +kernel)

theorem comm_8192_1263616 : ⁅normalForm 8192, normalForm 1263616⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 8192 1263616 1048576 17 (by decide +kernel)

theorem comm_8192_1312272 : ⁅normalForm 8192, normalForm 1312272⁆ = normalForm 524288 :=
  normalForm_commutator_of_collect 8192 1312272 524288 18 (by decide +kernel)

theorem comm_8192_1319936 : ⁅normalForm 8192, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 1319936 0 8 (by decide +kernel)

theorem comm_8192_1376320 : ⁅normalForm 8192, normalForm 1376320⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 8192 1376320 1572864 19 (by decide +kernel)

theorem comm_8192_1377808 : ⁅normalForm 8192, normalForm 1377808⁆ = normalForm 524288 :=
  normalForm_commutator_of_collect 8192 1377808 524288 22 (by decide +kernel)

theorem comm_8192_1489992 : ⁅normalForm 8192, normalForm 1489992⁆ = normalForm 1376256 :=
  normalForm_commutator_of_collect 8192 1489992 1376256 67 (by decide +kernel)

theorem comm_8192_1634560 : ⁅normalForm 8192, normalForm 1634560⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 8192 1634560 1048576 22 (by decide +kernel)

theorem comm_8192_1638464 : ⁅normalForm 8192, normalForm 1638464⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 8192 1638464 1572864 15 (by decide +kernel)

theorem comm_8192_1639952 : ⁅normalForm 8192, normalForm 1639952⁆ = normalForm 524288 :=
  normalForm_commutator_of_collect 8192 1639952 524288 18 (by decide +kernel)

theorem comm_8192_1765409 : ⁅normalForm 8192, normalForm 1765409⁆ = normalForm 2031616 :=
  normalForm_commutator_of_collect 8192 1765409 2031616 95 (by decide +kernel)

theorem comm_8192_1777920 : ⁅normalForm 8192, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 8192 1777920 0 12 (by decide +kernel)

theorem comm_16384_32768 : ⁅normalForm 16384, normalForm 32768⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 32768 0 3 (by decide +kernel)

theorem comm_16384_32832 : ⁅normalForm 16384, normalForm 32832⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 32832 0 5 (by decide +kernel)

theorem comm_16384_65536 : ⁅normalForm 16384, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 65536 0 3 (by decide +kernel)

theorem comm_16384_67584 : ⁅normalForm 16384, normalForm 67584⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 67584 0 5 (by decide +kernel)

theorem comm_16384_131072 : ⁅normalForm 16384, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 131072 0 3 (by decide +kernel)

theorem comm_16384_176200 : ⁅normalForm 16384, normalForm 176200⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 176200 0 19 (by decide +kernel)

theorem comm_16384_262144 : ⁅normalForm 16384, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 262144 0 3 (by decide +kernel)

theorem comm_16384_344576 : ⁅normalForm 16384, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 344576 0 8 (by decide +kernel)

theorem comm_16384_524288 : ⁅normalForm 16384, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 524288 0 3 (by decide +kernel)

theorem comm_16384_525312 : ⁅normalForm 16384, normalForm 525312⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 16384 525312 1048576 9 (by decide +kernel)

theorem comm_16384_606720 : ⁅normalForm 16384, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 606720 0 8 (by decide +kernel)

theorem comm_16384_664576 : ⁅normalForm 16384, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 664576 0 11 (by decide +kernel)

theorem comm_16384_804864 : ⁅normalForm 16384, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 804864 0 8 (by decide +kernel)

theorem comm_16384_1048576 : ⁅normalForm 16384, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1048576 0 3 (by decide +kernel)

theorem comm_16384_1090560 : ⁅normalForm 16384, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1090560 0 11 (by decide +kernel)

theorem comm_16384_1105480 : ⁅normalForm 16384, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1105480 0 24 (by decide +kernel)

theorem comm_16384_1179937 : ⁅normalForm 16384, normalForm 1179937⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1179937 0 14 (by decide +kernel)

theorem comm_16384_1198080 : ⁅normalForm 16384, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1198080 0 8 (by decide +kernel)

theorem comm_16384_1263616 : ⁅normalForm 16384, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1263616 0 10 (by decide +kernel)

theorem comm_16384_1312272 : ⁅normalForm 16384, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1312272 0 14 (by decide +kernel)

theorem comm_16384_1319936 : ⁅normalForm 16384, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1319936 0 11 (by decide +kernel)

theorem comm_16384_1376320 : ⁅normalForm 16384, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1376320 0 9 (by decide +kernel)

theorem comm_16384_1377808 : ⁅normalForm 16384, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1377808 0 16 (by decide +kernel)

theorem comm_16384_1489992 : ⁅normalForm 16384, normalForm 1489992⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 16384 1489992 1048576 38 (by decide +kernel)

theorem comm_16384_1634560 : ⁅normalForm 16384, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1634560 0 17 (by decide +kernel)

theorem comm_16384_1638464 : ⁅normalForm 16384, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1638464 0 9 (by decide +kernel)

theorem comm_16384_1639952 : ⁅normalForm 16384, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1639952 0 16 (by decide +kernel)

theorem comm_16384_1765409 : ⁅normalForm 16384, normalForm 1765409⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1765409 0 22 (by decide +kernel)

theorem comm_16384_1777920 : ⁅normalForm 16384, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 16384 1777920 0 15 (by decide +kernel)

theorem comm_32768_32832 : ⁅normalForm 32768, normalForm 32832⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 32768 32832 1572864 12 (by decide +kernel)

theorem comm_32768_65536 : ⁅normalForm 32768, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 65536 0 3 (by decide +kernel)

theorem comm_32768_67584 : ⁅normalForm 32768, normalForm 67584⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 32768 67584 1048576 9 (by decide +kernel)

theorem comm_32768_131072 : ⁅normalForm 32768, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 131072 0 3 (by decide +kernel)

theorem comm_32768_176200 : ⁅normalForm 32768, normalForm 176200⁆ = normalForm 1310720 :=
  normalForm_commutator_of_collect 32768 176200 1310720 45 (by decide +kernel)

theorem comm_32768_262144 : ⁅normalForm 32768, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 262144 0 3 (by decide +kernel)

theorem comm_32768_344576 : ⁅normalForm 32768, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 344576 0 9 (by decide +kernel)

theorem comm_32768_524288 : ⁅normalForm 32768, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 524288 0 3 (by decide +kernel)

theorem comm_32768_525312 : ⁅normalForm 32768, normalForm 525312⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 525312 0 5 (by decide +kernel)

theorem comm_32768_606720 : ⁅normalForm 32768, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 606720 0 9 (by decide +kernel)

theorem comm_32768_664576 : ⁅normalForm 32768, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 664576 0 9 (by decide +kernel)

theorem comm_32768_804864 : ⁅normalForm 32768, normalForm 804864⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 32768 804864 1048576 17 (by decide +kernel)

theorem comm_32768_1048576 : ⁅normalForm 32768, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1048576 0 3 (by decide +kernel)

theorem comm_32768_1090560 : ⁅normalForm 32768, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1090560 0 8 (by decide +kernel)

theorem comm_32768_1105480 : ⁅normalForm 32768, normalForm 1105480⁆ = normalForm 262144 :=
  normalForm_commutator_of_collect 32768 1105480 262144 48 (by decide +kernel)

theorem comm_32768_1179937 : ⁅normalForm 32768, normalForm 1179937⁆ = normalForm 1900544 :=
  normalForm_commutator_of_collect 32768 1179937 1900544 52 (by decide +kernel)

theorem comm_32768_1198080 : ⁅normalForm 32768, normalForm 1198080⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 32768 1198080 1048576 13 (by decide +kernel)

theorem comm_32768_1263616 : ⁅normalForm 32768, normalForm 1263616⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 32768 1263616 1048576 17 (by decide +kernel)

theorem comm_32768_1312272 : ⁅normalForm 32768, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1312272 0 11 (by decide +kernel)

theorem comm_32768_1319936 : ⁅normalForm 32768, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1319936 0 9 (by decide +kernel)

theorem comm_32768_1376320 : ⁅normalForm 32768, normalForm 1376320⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 32768 1376320 1572864 19 (by decide +kernel)

theorem comm_32768_1377808 : ⁅normalForm 32768, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1377808 0 13 (by decide +kernel)

theorem comm_32768_1489992 : ⁅normalForm 32768, normalForm 1489992⁆ = normalForm 262144 :=
  normalForm_commutator_of_collect 32768 1489992 262144 47 (by decide +kernel)

theorem comm_32768_1634560 : ⁅normalForm 32768, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1634560 0 14 (by decide +kernel)

theorem comm_32768_1638464 : ⁅normalForm 32768, normalForm 1638464⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 32768 1638464 1572864 15 (by decide +kernel)

theorem comm_32768_1639952 : ⁅normalForm 32768, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1639952 0 13 (by decide +kernel)

theorem comm_32768_1765409 : ⁅normalForm 32768, normalForm 1765409⁆ = normalForm 1900544 :=
  normalForm_commutator_of_collect 32768 1765409 1900544 82 (by decide +kernel)

theorem comm_32768_1777920 : ⁅normalForm 32768, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32768 1777920 0 13 (by decide +kernel)

theorem comm_32832_65536 : ⁅normalForm 32832, normalForm 65536⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32832 65536 0 5 (by decide +kernel)

theorem comm_32832_131072 : ⁅normalForm 32832, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32832 131072 0 5 (by decide +kernel)

theorem comm_32832_176200 : ⁅normalForm 32832, normalForm 176200⁆ = normalForm 1310720 :=
  normalForm_commutator_of_collect 32832 176200 1310720 68 (by decide +kernel)

theorem comm_32832_262144 : ⁅normalForm 32832, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32832 262144 0 5 (by decide +kernel)

theorem comm_32832_344576 : ⁅normalForm 32832, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32832 344576 0 14 (by decide +kernel)

theorem comm_32832_524288 : ⁅normalForm 32832, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32832 524288 0 5 (by decide +kernel)

theorem comm_32832_606720 : ⁅normalForm 32832, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32832 606720 0 14 (by decide +kernel)

theorem comm_32832_664576 : ⁅normalForm 32832, normalForm 664576⁆ = normalForm 1966080 :=
  normalForm_commutator_of_collect 32832 664576 1966080 32 (by decide +kernel)

theorem comm_32832_1048576 : ⁅normalForm 32832, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 32832 1048576 0 5 (by decide +kernel)

theorem comm_32832_1105480 : ⁅normalForm 32832, normalForm 1105480⁆ = normalForm 1703936 :=
  normalForm_commutator_of_collect 32832 1105480 1703936 98 (by decide +kernel)

theorem comm_32832_1179937 : ⁅normalForm 32832, normalForm 1179937⁆ = normalForm 1966080 :=
  normalForm_commutator_of_collect 32832 1179937 1966080 84 (by decide +kernel)

theorem comm_32832_1198080 : ⁅normalForm 32832, normalForm 1198080⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 32832 1198080 1048576 17 (by decide +kernel)

theorem comm_32832_1263616 : ⁅normalForm 32832, normalForm 1263616⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 32832 1263616 1048576 22 (by decide +kernel)

theorem comm_32832_1312272 : ⁅normalForm 32832, normalForm 1312272⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 32832 1312272 1572864 42 (by decide +kernel)

theorem comm_32832_1377808 : ⁅normalForm 32832, normalForm 1377808⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 32832 1377808 1572864 53 (by decide +kernel)

theorem comm_32832_1765409 : ⁅normalForm 32832, normalForm 1765409⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 32832 1765409 1572864 106 (by decide +kernel)

theorem comm_32832_1777920 : ⁅normalForm 32832, normalForm 1777920⁆ = normalForm 720896 :=
  normalForm_commutator_of_collect 32832 1777920 720896 37 (by decide +kernel)

theorem comm_65536_67584 : ⁅normalForm 65536, normalForm 67584⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 67584 0 4 (by decide +kernel)

theorem comm_65536_131072 : ⁅normalForm 65536, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 131072 0 3 (by decide +kernel)

theorem comm_65536_176200 : ⁅normalForm 65536, normalForm 176200⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 176200 0 15 (by decide +kernel)

theorem comm_65536_262144 : ⁅normalForm 65536, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 262144 0 3 (by decide +kernel)

theorem comm_65536_344576 : ⁅normalForm 65536, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 344576 0 8 (by decide +kernel)

theorem comm_65536_524288 : ⁅normalForm 65536, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 524288 0 3 (by decide +kernel)

theorem comm_65536_525312 : ⁅normalForm 65536, normalForm 525312⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 525312 1048576 9 (by decide +kernel)

theorem comm_65536_606720 : ⁅normalForm 65536, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 606720 0 8 (by decide +kernel)

theorem comm_65536_664576 : ⁅normalForm 65536, normalForm 664576⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 664576 1048576 17 (by decide +kernel)

theorem comm_65536_804864 : ⁅normalForm 65536, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 804864 0 9 (by decide +kernel)

theorem comm_65536_1048576 : ⁅normalForm 65536, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 1048576 0 3 (by decide +kernel)

theorem comm_65536_1090560 : ⁅normalForm 65536, normalForm 1090560⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 1090560 1048576 13 (by decide +kernel)

theorem comm_65536_1105480 : ⁅normalForm 65536, normalForm 1105480⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 1105480 1048576 33 (by decide +kernel)

theorem comm_65536_1179937 : ⁅normalForm 65536, normalForm 1179937⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 1179937 1048576 19 (by decide +kernel)

theorem comm_65536_1198080 : ⁅normalForm 65536, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 1198080 0 9 (by decide +kernel)

theorem comm_65536_1263616 : ⁅normalForm 65536, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 1263616 0 10 (by decide +kernel)

theorem comm_65536_1312272 : ⁅normalForm 65536, normalForm 1312272⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 65536 1312272 1572864 24 (by decide +kernel)

theorem comm_65536_1319936 : ⁅normalForm 65536, normalForm 1319936⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 1319936 1048576 13 (by decide +kernel)

theorem comm_65536_1376320 : ⁅normalForm 65536, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 1376320 0 8 (by decide +kernel)

theorem comm_65536_1377808 : ⁅normalForm 65536, normalForm 1377808⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 65536 1377808 1572864 29 (by decide +kernel)

theorem comm_65536_1489992 : ⁅normalForm 65536, normalForm 1489992⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 1489992 1048576 38 (by decide +kernel)

theorem comm_65536_1634560 : ⁅normalForm 65536, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 1634560 0 15 (by decide +kernel)

theorem comm_65536_1638464 : ⁅normalForm 65536, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 1638464 0 8 (by decide +kernel)

theorem comm_65536_1639952 : ⁅normalForm 65536, normalForm 1639952⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 65536 1639952 1572864 25 (by decide +kernel)

theorem comm_65536_1765409 : ⁅normalForm 65536, normalForm 1765409⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 65536 1765409 1048576 35 (by decide +kernel)

theorem comm_65536_1777920 : ⁅normalForm 65536, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 65536 1777920 0 12 (by decide +kernel)

theorem comm_67584_131072 : ⁅normalForm 67584, normalForm 131072⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 131072 0 5 (by decide +kernel)

theorem comm_67584_262144 : ⁅normalForm 67584, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 262144 0 5 (by decide +kernel)

theorem comm_67584_344576 : ⁅normalForm 67584, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 344576 0 13 (by decide +kernel)

theorem comm_67584_524288 : ⁅normalForm 67584, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 524288 0 5 (by decide +kernel)

theorem comm_67584_525312 : ⁅normalForm 67584, normalForm 525312⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 67584 525312 1048576 13 (by decide +kernel)

theorem comm_67584_1048576 : ⁅normalForm 67584, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 1048576 0 5 (by decide +kernel)

theorem comm_67584_1263616 : ⁅normalForm 67584, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 1263616 0 15 (by decide +kernel)

theorem comm_67584_1312272 : ⁅normalForm 67584, normalForm 1312272⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 67584 1312272 1441792 36 (by decide +kernel)

theorem comm_67584_1376320 : ⁅normalForm 67584, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 1376320 0 13 (by decide +kernel)

theorem comm_67584_1489992 : ⁅normalForm 67584, normalForm 1489992⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 67584 1489992 1048576 49 (by decide +kernel)

theorem comm_67584_1634560 : ⁅normalForm 67584, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 67584 1634560 0 29 (by decide +kernel)

theorem comm_131072_176200 : ⁅normalForm 131072, normalForm 176200⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 176200 0 17 (by decide +kernel)

theorem comm_131072_262144 : ⁅normalForm 131072, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 262144 0 3 (by decide +kernel)

theorem comm_131072_344576 : ⁅normalForm 131072, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 344576 0 9 (by decide +kernel)

theorem comm_131072_524288 : ⁅normalForm 131072, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 524288 0 3 (by decide +kernel)

theorem comm_131072_525312 : ⁅normalForm 131072, normalForm 525312⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 525312 0 5 (by decide +kernel)

theorem comm_131072_606720 : ⁅normalForm 131072, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 606720 0 9 (by decide +kernel)

theorem comm_131072_664576 : ⁅normalForm 131072, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 664576 0 8 (by decide +kernel)

theorem comm_131072_804864 : ⁅normalForm 131072, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 804864 0 9 (by decide +kernel)

theorem comm_131072_1048576 : ⁅normalForm 131072, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1048576 0 3 (by decide +kernel)

theorem comm_131072_1090560 : ⁅normalForm 131072, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1090560 0 9 (by decide +kernel)

theorem comm_131072_1105480 : ⁅normalForm 131072, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1105480 0 27 (by decide +kernel)

theorem comm_131072_1179937 : ⁅normalForm 131072, normalForm 1179937⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 131072 1179937 1048576 18 (by decide +kernel)

theorem comm_131072_1198080 : ⁅normalForm 131072, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1198080 0 8 (by decide +kernel)

theorem comm_131072_1263616 : ⁅normalForm 131072, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1263616 0 10 (by decide +kernel)

theorem comm_131072_1312272 : ⁅normalForm 131072, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1312272 0 11 (by decide +kernel)

theorem comm_131072_1319936 : ⁅normalForm 131072, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1319936 0 9 (by decide +kernel)

theorem comm_131072_1376320 : ⁅normalForm 131072, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1376320 0 9 (by decide +kernel)

theorem comm_131072_1377808 : ⁅normalForm 131072, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1377808 0 13 (by decide +kernel)

theorem comm_131072_1489992 : ⁅normalForm 131072, normalForm 1489992⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1489992 0 27 (by decide +kernel)

theorem comm_131072_1634560 : ⁅normalForm 131072, normalForm 1634560⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 131072 1634560 1048576 24 (by decide +kernel)

theorem comm_131072_1638464 : ⁅normalForm 131072, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1638464 0 9 (by decide +kernel)

theorem comm_131072_1639952 : ⁅normalForm 131072, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1639952 0 13 (by decide +kernel)

theorem comm_131072_1765409 : ⁅normalForm 131072, normalForm 1765409⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1765409 0 22 (by decide +kernel)

theorem comm_131072_1777920 : ⁅normalForm 131072, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 131072 1777920 0 12 (by decide +kernel)

theorem comm_176200_262144 : ⁅normalForm 176200, normalForm 262144⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 176200 262144 0 17 (by decide +kernel)

theorem comm_176200_524288 : ⁅normalForm 176200, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 176200 524288 0 17 (by decide +kernel)

theorem comm_176200_606720 : ⁅normalForm 176200, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 176200 606720 0 65 (by decide +kernel)

theorem comm_176200_1048576 : ⁅normalForm 176200, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 176200 1048576 0 16 (by decide +kernel)

theorem comm_176200_1179937 : ⁅normalForm 176200, normalForm 1179937⁆ = normalForm 737280 :=
  normalForm_commutator_of_collect 176200 1179937 737280 169 (by decide +kernel)

theorem comm_176200_1263616 : ⁅normalForm 176200, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 176200 1263616 0 53 (by decide +kernel)

theorem comm_176200_1312272 : ⁅normalForm 176200, normalForm 1312272⁆ = normalForm 606720 :=
  normalForm_commutator_of_collect 176200 1312272 606720 136 (by decide +kernel)

theorem comm_262144_344576 : ⁅normalForm 262144, normalForm 344576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 344576 0 8 (by decide +kernel)

theorem comm_262144_524288 : ⁅normalForm 262144, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 524288 0 3 (by decide +kernel)

theorem comm_262144_525312 : ⁅normalForm 262144, normalForm 525312⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 525312 0 5 (by decide +kernel)

theorem comm_262144_606720 : ⁅normalForm 262144, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 606720 0 9 (by decide +kernel)

theorem comm_262144_664576 : ⁅normalForm 262144, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 664576 0 9 (by decide +kernel)

theorem comm_262144_804864 : ⁅normalForm 262144, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 804864 0 8 (by decide +kernel)

theorem comm_262144_1048576 : ⁅normalForm 262144, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1048576 0 3 (by decide +kernel)

theorem comm_262144_1090560 : ⁅normalForm 262144, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1090560 0 9 (by decide +kernel)

theorem comm_262144_1105480 : ⁅normalForm 262144, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1105480 0 21 (by decide +kernel)

theorem comm_262144_1179937 : ⁅normalForm 262144, normalForm 1179937⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1179937 0 14 (by decide +kernel)

theorem comm_262144_1198080 : ⁅normalForm 262144, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1198080 0 9 (by decide +kernel)

theorem comm_262144_1263616 : ⁅normalForm 262144, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1263616 0 11 (by decide +kernel)

theorem comm_262144_1312272 : ⁅normalForm 262144, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1312272 0 10 (by decide +kernel)

theorem comm_262144_1319936 : ⁅normalForm 262144, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1319936 0 8 (by decide +kernel)

theorem comm_262144_1376320 : ⁅normalForm 262144, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1376320 0 8 (by decide +kernel)

theorem comm_262144_1377808 : ⁅normalForm 262144, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1377808 0 12 (by decide +kernel)

theorem comm_262144_1489992 : ⁅normalForm 262144, normalForm 1489992⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1489992 0 22 (by decide +kernel)

theorem comm_262144_1634560 : ⁅normalForm 262144, normalForm 1634560⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 262144 1634560 1048576 25 (by decide +kernel)

theorem comm_262144_1638464 : ⁅normalForm 262144, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1638464 0 9 (by decide +kernel)

theorem comm_262144_1639952 : ⁅normalForm 262144, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 262144 1639952 0 13 (by decide +kernel)

theorem comm_262144_1765409 : ⁅normalForm 262144, normalForm 1765409⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 262144 1765409 1048576 34 (by decide +kernel)

theorem comm_262144_1777920 : ⁅normalForm 262144, normalForm 1777920⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 262144 1777920 1048576 21 (by decide +kernel)

theorem comm_344576_524288 : ⁅normalForm 344576, normalForm 524288⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 524288 0 9 (by decide +kernel)

theorem comm_344576_525312 : ⁅normalForm 344576, normalForm 525312⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 344576 525312 1572864 20 (by decide +kernel)

theorem comm_344576_606720 : ⁅normalForm 344576, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 606720 0 21 (by decide +kernel)

theorem comm_344576_664576 : ⁅normalForm 344576, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 664576 0 41 (by decide +kernel)

theorem comm_344576_804864 : ⁅normalForm 344576, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 804864 0 22 (by decide +kernel)

theorem comm_344576_1048576 : ⁅normalForm 344576, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1048576 0 9 (by decide +kernel)

theorem comm_344576_1090560 : ⁅normalForm 344576, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1090560 0 31 (by decide +kernel)

theorem comm_344576_1105480 : ⁅normalForm 344576, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1105480 0 69 (by decide +kernel)

theorem comm_344576_1198080 : ⁅normalForm 344576, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1198080 0 23 (by decide +kernel)

theorem comm_344576_1263616 : ⁅normalForm 344576, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1263616 0 27 (by decide +kernel)

theorem comm_344576_1312272 : ⁅normalForm 344576, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1312272 0 44 (by decide +kernel)

theorem comm_344576_1319936 : ⁅normalForm 344576, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1319936 0 30 (by decide +kernel)

theorem comm_344576_1376320 : ⁅normalForm 344576, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1376320 0 22 (by decide +kernel)

theorem comm_344576_1377808 : ⁅normalForm 344576, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1377808 0 52 (by decide +kernel)

theorem comm_344576_1489992 : ⁅normalForm 344576, normalForm 1489992⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 344576 1489992 1572864 97 (by decide +kernel)

theorem comm_344576_1634560 : ⁅normalForm 344576, normalForm 1634560⁆ = normalForm 393216 :=
  normalForm_commutator_of_collect 344576 1634560 393216 75 (by decide +kernel)

theorem comm_344576_1638464 : ⁅normalForm 344576, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1638464 0 23 (by decide +kernel)

theorem comm_344576_1639952 : ⁅normalForm 344576, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 344576 1639952 0 41 (by decide +kernel)

theorem comm_344576_1765409 : ⁅normalForm 344576, normalForm 1765409⁆ = normalForm 1703936 :=
  normalForm_commutator_of_collect 344576 1765409 1703936 104 (by decide +kernel)

theorem comm_344576_1777920 : ⁅normalForm 344576, normalForm 1777920⁆ = normalForm 1703936 :=
  normalForm_commutator_of_collect 344576 1777920 1703936 52 (by decide +kernel)

theorem comm_524288_525312 : ⁅normalForm 524288, normalForm 525312⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 525312 0 4 (by decide +kernel)

theorem comm_524288_606720 : ⁅normalForm 524288, normalForm 606720⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 606720 0 8 (by decide +kernel)

theorem comm_524288_664576 : ⁅normalForm 524288, normalForm 664576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 664576 0 8 (by decide +kernel)

theorem comm_524288_804864 : ⁅normalForm 524288, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 804864 0 8 (by decide +kernel)

theorem comm_524288_1048576 : ⁅normalForm 524288, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1048576 0 3 (by decide +kernel)

theorem comm_524288_1090560 : ⁅normalForm 524288, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1090560 0 9 (by decide +kernel)

theorem comm_524288_1105480 : ⁅normalForm 524288, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1105480 0 21 (by decide +kernel)

theorem comm_524288_1179937 : ⁅normalForm 524288, normalForm 1179937⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1179937 0 14 (by decide +kernel)

theorem comm_524288_1198080 : ⁅normalForm 524288, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1198080 0 9 (by decide +kernel)

theorem comm_524288_1263616 : ⁅normalForm 524288, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1263616 0 11 (by decide +kernel)

theorem comm_524288_1312272 : ⁅normalForm 524288, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1312272 0 11 (by decide +kernel)

theorem comm_524288_1319936 : ⁅normalForm 524288, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1319936 0 9 (by decide +kernel)

theorem comm_524288_1376320 : ⁅normalForm 524288, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1376320 0 9 (by decide +kernel)

theorem comm_524288_1377808 : ⁅normalForm 524288, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1377808 0 13 (by decide +kernel)

theorem comm_524288_1489992 : ⁅normalForm 524288, normalForm 1489992⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1489992 0 23 (by decide +kernel)

theorem comm_524288_1634560 : ⁅normalForm 524288, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1634560 0 14 (by decide +kernel)

theorem comm_524288_1638464 : ⁅normalForm 524288, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1638464 0 8 (by decide +kernel)

theorem comm_524288_1639952 : ⁅normalForm 524288, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1639952 0 12 (by decide +kernel)

theorem comm_524288_1765409 : ⁅normalForm 524288, normalForm 1765409⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1765409 0 21 (by decide +kernel)

theorem comm_524288_1777920 : ⁅normalForm 524288, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 524288 1777920 0 12 (by decide +kernel)

theorem comm_525312_606720 : ⁅normalForm 525312, normalForm 606720⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 525312 606720 1572864 25 (by decide +kernel)

theorem comm_525312_1048576 : ⁅normalForm 525312, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 525312 1048576 0 5 (by decide +kernel)

theorem comm_525312_1090560 : ⁅normalForm 525312, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 525312 1090560 0 13 (by decide +kernel)

theorem comm_525312_1105480 : ⁅normalForm 525312, normalForm 1105480⁆ = normalForm 1523712 :=
  normalForm_commutator_of_collect 525312 1105480 1523712 123 (by decide +kernel)

theorem comm_525312_1263616 : ⁅normalForm 525312, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 525312 1263616 0 19 (by decide +kernel)

theorem comm_525312_1312272 : ⁅normalForm 525312, normalForm 1312272⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 525312 1312272 1572864 24 (by decide +kernel)

theorem comm_525312_1376320 : ⁅normalForm 525312, normalForm 1376320⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 525312 1376320 1441792 24 (by decide +kernel)

theorem comm_525312_1489992 : ⁅normalForm 525312, normalForm 1489992⁆ = normalForm 2048000 :=
  normalForm_commutator_of_collect 525312 1489992 2048000 131 (by decide +kernel)

theorem comm_525312_1634560 : ⁅normalForm 525312, normalForm 1634560⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 525312 1634560 1048576 30 (by decide +kernel)

theorem comm_525312_1638464 : ⁅normalForm 525312, normalForm 1638464⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 525312 1638464 1441792 27 (by decide +kernel)

theorem comm_525312_1639952 : ⁅normalForm 525312, normalForm 1639952⁆ = normalForm 524288 :=
  normalForm_commutator_of_collect 525312 1639952 524288 22 (by decide +kernel)

theorem comm_606720_1048576 : ⁅normalForm 606720, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 606720 1048576 0 9 (by decide +kernel)

theorem comm_606720_1179937 : ⁅normalForm 606720, normalForm 1179937⁆ = normalForm 786432 :=
  normalForm_commutator_of_collect 606720 1179937 786432 73 (by decide +kernel)

theorem comm_606720_1263616 : ⁅normalForm 606720, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 606720 1263616 0 27 (by decide +kernel)

theorem comm_606720_1312272 : ⁅normalForm 606720, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 606720 1312272 0 37 (by decide +kernel)

theorem comm_606720_1376320 : ⁅normalForm 606720, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 606720 1376320 0 23 (by decide +kernel)

theorem comm_606720_1489992 : ⁅normalForm 606720, normalForm 1489992⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 606720 1489992 1572864 114 (by decide +kernel)

theorem comm_606720_1634560 : ⁅normalForm 606720, normalForm 1634560⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 606720 1634560 1441792 76 (by decide +kernel)

theorem comm_664576_804864 : ⁅normalForm 664576, normalForm 804864⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 664576 804864 0 29 (by decide +kernel)

theorem comm_664576_1048576 : ⁅normalForm 664576, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 664576 1048576 0 9 (by decide +kernel)

theorem comm_664576_1105480 : ⁅normalForm 664576, normalForm 1105480⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 664576 1105480 671744 116 (by decide +kernel)

theorem comm_664576_1198080 : ⁅normalForm 664576, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 664576 1198080 0 25 (by decide +kernel)

theorem comm_664576_1319936 : ⁅normalForm 664576, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 664576 1319936 0 22 (by decide +kernel)

theorem comm_664576_1377808 : ⁅normalForm 664576, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 664576 1377808 0 40 (by decide +kernel)

theorem comm_664576_1765409 : ⁅normalForm 664576, normalForm 1765409⁆ = normalForm 1853440 :=
  normalForm_commutator_of_collect 664576 1765409 1853440 111 (by decide +kernel)

theorem comm_664576_1777920 : ⁅normalForm 664576, normalForm 1777920⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 664576 1777920 1048576 38 (by decide +kernel)

theorem comm_804864_1048576 : ⁅normalForm 804864, normalForm 1048576⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 804864 1048576 0 9 (by decide +kernel)

theorem comm_804864_1105480 : ⁅normalForm 804864, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 804864 1105480 0 54 (by decide +kernel)

theorem comm_804864_1198080 : ⁅normalForm 804864, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 804864 1198080 0 22 (by decide +kernel)

theorem comm_804864_1377808 : ⁅normalForm 804864, normalForm 1377808⁆ = normalForm 917504 :=
  normalForm_commutator_of_collect 804864 1377808 917504 55 (by decide +kernel)

theorem comm_804864_1765409 : ⁅normalForm 804864, normalForm 1765409⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 804864 1765409 0 61 (by decide +kernel)

theorem comm_804864_1777920 : ⁅normalForm 804864, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 804864 1777920 0 40 (by decide +kernel)

theorem comm_1048576_1090560 : ⁅normalForm 1048576, normalForm 1090560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1090560 0 8 (by decide +kernel)

theorem comm_1048576_1105480 : ⁅normalForm 1048576, normalForm 1105480⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1105480 0 20 (by decide +kernel)

theorem comm_1048576_1179937 : ⁅normalForm 1048576, normalForm 1179937⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1179937 0 11 (by decide +kernel)

theorem comm_1048576_1198080 : ⁅normalForm 1048576, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1198080 0 8 (by decide +kernel)

theorem comm_1048576_1263616 : ⁅normalForm 1048576, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1263616 0 10 (by decide +kernel)

theorem comm_1048576_1312272 : ⁅normalForm 1048576, normalForm 1312272⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1312272 0 10 (by decide +kernel)

theorem comm_1048576_1319936 : ⁅normalForm 1048576, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1319936 0 8 (by decide +kernel)

theorem comm_1048576_1376320 : ⁅normalForm 1048576, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1376320 0 8 (by decide +kernel)

theorem comm_1048576_1377808 : ⁅normalForm 1048576, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1377808 0 12 (by decide +kernel)

theorem comm_1048576_1489992 : ⁅normalForm 1048576, normalForm 1489992⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1489992 0 22 (by decide +kernel)

theorem comm_1048576_1634560 : ⁅normalForm 1048576, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1634560 0 14 (by decide +kernel)

theorem comm_1048576_1638464 : ⁅normalForm 1048576, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1638464 0 8 (by decide +kernel)

theorem comm_1048576_1639952 : ⁅normalForm 1048576, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1639952 0 12 (by decide +kernel)

theorem comm_1048576_1765409 : ⁅normalForm 1048576, normalForm 1765409⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1765409 0 19 (by decide +kernel)

theorem comm_1048576_1777920 : ⁅normalForm 1048576, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1048576 1777920 0 12 (by decide +kernel)

theorem comm_1090560_1263616 : ⁅normalForm 1090560, normalForm 1263616⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1090560 1263616 0 28 (by decide +kernel)

theorem comm_1090560_1312272 : ⁅normalForm 1090560, normalForm 1312272⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1090560 1312272 1048576 31 (by decide +kernel)

theorem comm_1090560_1376320 : ⁅normalForm 1090560, normalForm 1376320⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 1090560 1376320 1441792 42 (by decide +kernel)

theorem comm_1090560_1489992 : ⁅normalForm 1090560, normalForm 1489992⁆ = normalForm 1982464 :=
  normalForm_commutator_of_collect 1090560 1489992 1982464 169 (by decide +kernel)

theorem comm_1090560_1634560 : ⁅normalForm 1090560, normalForm 1634560⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1090560 1634560 0 40 (by decide +kernel)

theorem comm_1105480_1198080 : ⁅normalForm 1105480, normalForm 1198080⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1105480 1198080 0 50 (by decide +kernel)

theorem comm_1105480_1263616 : ⁅normalForm 1105480, normalForm 1263616⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1105480 1263616 1048576 66 (by decide +kernel)

theorem comm_1105480_1312272 : ⁅normalForm 1105480, normalForm 1312272⁆ = normalForm 999936 :=
  normalForm_commutator_of_collect 1105480 1312272 999936 159 (by decide +kernel)

theorem comm_1105480_1319936 : ⁅normalForm 1105480, normalForm 1319936⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 1105480 1319936 671744 94 (by decide +kernel)

theorem comm_1105480_1376320 : ⁅normalForm 1105480, normalForm 1376320⁆ = normalForm 917504 :=
  normalForm_commutator_of_collect 1105480 1376320 917504 92 (by decide +kernel)

theorem comm_1105480_1377808 : ⁅normalForm 1105480, normalForm 1377808⁆ = normalForm 2048512 :=
  normalForm_commutator_of_collect 1105480 1377808 2048512 178 (by decide +kernel)

theorem comm_1105480_1489992 : ⁅normalForm 1105480, normalForm 1489992⁆ = normalForm 851968 :=
  normalForm_commutator_of_collect 1105480 1489992 851968 292 (by decide +kernel)

theorem comm_1105480_1634560 : ⁅normalForm 1105480, normalForm 1634560⁆ = normalForm 83968 :=
  normalForm_commutator_of_collect 1105480 1634560 83968 172 (by decide +kernel)

theorem comm_1105480_1765409 : ⁅normalForm 1105480, normalForm 1765409⁆ = normalForm 671744 :=
  normalForm_commutator_of_collect 1105480 1765409 671744 201 (by decide +kernel)

theorem comm_1105480_1777920 : ⁅normalForm 1105480, normalForm 1777920⁆ = normalForm 804864 :=
  normalForm_commutator_of_collect 1105480 1777920 804864 120 (by decide +kernel)

theorem comm_1179937_1263616 : ⁅normalForm 1179937, normalForm 1263616⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1179937 1263616 1048576 48 (by decide +kernel)

theorem comm_1179937_1312272 : ⁅normalForm 1179937, normalForm 1312272⁆ = normalForm 1998912 :=
  normalForm_commutator_of_collect 1179937 1312272 1998912 133 (by decide +kernel)

theorem comm_1198080_1319936 : ⁅normalForm 1198080, normalForm 1319936⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1198080 1319936 0 25 (by decide +kernel)

theorem comm_1198080_1377808 : ⁅normalForm 1198080, normalForm 1377808⁆ = normalForm 917504 :=
  normalForm_commutator_of_collect 1198080 1377808 917504 59 (by decide +kernel)

theorem comm_1198080_1765409 : ⁅normalForm 1198080, normalForm 1765409⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1198080 1765409 1048576 64 (by decide +kernel)

theorem comm_1198080_1777920 : ⁅normalForm 1198080, normalForm 1777920⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1198080 1777920 1048576 34 (by decide +kernel)

theorem comm_1263616_1312272 : ⁅normalForm 1263616, normalForm 1312272⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 1263616 1312272 1441792 49 (by decide +kernel)

theorem comm_1263616_1376320 : ⁅normalForm 1263616, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1263616 1376320 0 27 (by decide +kernel)

theorem comm_1263616_1489992 : ⁅normalForm 1263616, normalForm 1489992⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1263616 1489992 0 63 (by decide +kernel)

theorem comm_1263616_1634560 : ⁅normalForm 1263616, normalForm 1634560⁆ = normalForm 1048576 :=
  normalForm_commutator_of_collect 1263616 1634560 1048576 56 (by decide +kernel)

theorem comm_1263616_1638464 : ⁅normalForm 1263616, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1263616 1638464 0 27 (by decide +kernel)

theorem comm_1263616_1639952 : ⁅normalForm 1263616, normalForm 1639952⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 1263616 1639952 1441792 64 (by decide +kernel)

theorem comm_1312272_1376320 : ⁅normalForm 1312272, normalForm 1376320⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1312272 1376320 0 37 (by decide +kernel)

theorem comm_1312272_1489992 : ⁅normalForm 1312272, normalForm 1489992⁆ = normalForm 2048512 :=
  normalForm_commutator_of_collect 1312272 1489992 2048512 236 (by decide +kernel)

theorem comm_1312272_1634560 : ⁅normalForm 1312272, normalForm 1634560⁆ = normalForm 393216 :=
  normalForm_commutator_of_collect 1312272 1634560 393216 83 (by decide +kernel)

theorem comm_1312272_1638464 : ⁅normalForm 1312272, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1312272 1638464 0 48 (by decide +kernel)

theorem comm_1312272_1639952 : ⁅normalForm 1312272, normalForm 1639952⁆ = normalForm 1572864 :=
  normalForm_commutator_of_collect 1312272 1639952 1572864 45 (by decide +kernel)

theorem comm_1319936_1377808 : ⁅normalForm 1319936, normalForm 1377808⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1319936 1377808 0 32 (by decide +kernel)

theorem comm_1319936_1765409 : ⁅normalForm 1319936, normalForm 1765409⁆ = normalForm 804864 :=
  normalForm_commutator_of_collect 1319936 1765409 804864 98 (by decide +kernel)

theorem comm_1319936_1777920 : ⁅normalForm 1319936, normalForm 1777920⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1319936 1777920 0 28 (by decide +kernel)

theorem comm_1376320_1489992 : ⁅normalForm 1376320, normalForm 1489992⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 1376320 1489992 1441792 79 (by decide +kernel)

theorem comm_1376320_1634560 : ⁅normalForm 1376320, normalForm 1634560⁆ = normalForm 393216 :=
  normalForm_commutator_of_collect 1376320 1634560 393216 63 (by decide +kernel)

theorem comm_1376320_1638464 : ⁅normalForm 1376320, normalForm 1638464⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1376320 1638464 0 21 (by decide +kernel)

theorem comm_1376320_1639952 : ⁅normalForm 1376320, normalForm 1639952⁆ = normalForm 0 :=
  normalForm_commutator_of_collect 1376320 1639952 0 48 (by decide +kernel)

theorem comm_1377808_1765409 : ⁅normalForm 1377808, normalForm 1765409⁆ = normalForm 32832 :=
  normalForm_commutator_of_collect 1377808 1765409 32832 229 (by decide +kernel)

theorem comm_1377808_1777920 : ⁅normalForm 1377808, normalForm 1777920⁆ = normalForm 163840 :=
  normalForm_commutator_of_collect 1377808 1777920 163840 48 (by decide +kernel)

theorem comm_1489992_1634560 : ⁅normalForm 1489992, normalForm 1634560⁆ = normalForm 1525760 :=
  normalForm_commutator_of_collect 1489992 1634560 1525760 167 (by decide +kernel)

theorem comm_1489992_1638464 : ⁅normalForm 1489992, normalForm 1638464⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 1489992 1638464 1441792 88 (by decide +kernel)

theorem comm_1489992_1639952 : ⁅normalForm 1489992, normalForm 1639952⁆ = normalForm 999936 :=
  normalForm_commutator_of_collect 1489992 1639952 999936 196 (by decide +kernel)

theorem comm_1634560_1638464 : ⁅normalForm 1634560, normalForm 1638464⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 1634560 1638464 1441792 72 (by decide +kernel)

theorem comm_1634560_1639952 : ⁅normalForm 1634560, normalForm 1639952⁆ = normalForm 1441792 :=
  normalForm_commutator_of_collect 1634560 1639952 1441792 87 (by decide +kernel)

theorem comm_1765409_1777920 : ⁅normalForm 1765409, normalForm 1777920⁆ = normalForm 804864 :=
  normalForm_commutator_of_collect 1765409 1777920 804864 115 (by decide +kernel)

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms
