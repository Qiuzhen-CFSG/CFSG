module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Data

/-!
# The shared catalogue of 475 order-thirteen products

Source: Parrott (1972), section 5, p.683; `source/README.md`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ProductCertificates

-- The measured finite batches are checked sequentially to bound resident memory.
set_option Elab.async false

theorem orderBatch00 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 0 j)) (catalogueK (slot 0 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1738, 1754] 11 (by decide +kernel)
  · exact productTest_of_orderTest [884, 940] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1419, 1498] 11 (by decide +kernel)
  · exact productTest_of_orderTest [118, 181] 11 (by decide +kernel)
  · exact productTest_of_orderTest [768, 842] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1296, 1433] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1766, 1773] 11 (by decide +kernel)
  · exact productTest_of_orderTest [90, 751] 11 (by decide +kernel)
  · exact productTest_of_orderTest [109, 567] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1671, 1757] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1339, 1503] 11 (by decide +kernel)
  · exact productTest_of_orderTest [412, 929] 11 (by decide +kernel)
  · exact productTest_of_orderTest [213, 670] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1363, 1489] 11 (by decide +kernel)
  · exact productTest_of_orderTest [65, 602] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1163, 1561] 11 (by decide +kernel)
  · exact productTest_of_orderTest [591, 1748] 11 (by decide +kernel)
  · exact productTest_of_orderTest [341, 399] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1292, 2026] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1210, 1668] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1389, 1701] 11 (by decide +kernel)
  · exact productTest_of_orderTest [365, 1014] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1398, 1836] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1171, 1178] 12 (by decide +kernel)
  · exact productTest_of_orderTest [318, 444] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1074, 1146] 12 (by decide +kernel)
  · exact productTest_of_orderTest [181, 586] 12 (by decide +kernel)
  · exact productTest_of_orderTest [272, 402] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1196, 1198] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1184, 1211] 12 (by decide +kernel)
  · exact productTest_of_orderTest [27, 74] 12 (by decide +kernel)
  · exact productTest_of_orderTest [374, 886] 12 (by decide +kernel)

theorem orderBatch01 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 1 j)) (catalogueK (slot 1 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [415, 903] 12 (by decide +kernel)
  · exact productTest_of_orderTest [198, 747] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1125, 1133] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1346, 2044] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1442, 1991] 12 (by decide +kernel)
  · exact productTest_of_orderTest [921, 968] 12 (by decide +kernel)
  · exact productTest_of_orderTest [274, 986] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1166, 1180] 12 (by decide +kernel)
  · exact productTest_of_orderTest [867, 1009] 12 (by decide +kernel)
  · exact productTest_of_orderTest [644, 1298] 12 (by decide +kernel)
  · exact productTest_of_orderTest [1043, 1057] 12 (by decide +kernel)
  · exact productTest_of_orderTest [341, 1888] 12 (by decide +kernel)
  · exact productTest_of_orderTest [533, 591] 12 (by decide +kernel)
  · exact productTest_of_orderTest [144, 202] 14 (by decide +kernel)
  · exact productTest_of_orderTest [548, 638] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1960, 2025] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1711, 1774] 14 (by decide +kernel)
  · exact productTest_of_orderTest [130, 195] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1674, 1739] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1813, 1876] 14 (by decide +kernel)
  · exact productTest_of_orderTest [90, 766] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1268, 1728] 14 (by decide +kernel)
  · exact productTest_of_orderTest [685, 743] 14 (by decide +kernel)
  · exact productTest_of_orderTest [81, 193] 14 (by decide +kernel)
  · exact productTest_of_orderTest [514, 579] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1428, 2018] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1098, 1765] 14 (by decide +kernel)
  · exact productTest_of_orderTest [658, 712] 14 (by decide +kernel)
  · exact productTest_of_orderTest [144, 687] 14 (by decide +kernel)
  · exact productTest_of_orderTest [128, 139] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1337, 1442] 14 (by decide +kernel)
  · exact productTest_of_orderTest [137, 200] 14 (by decide +kernel)

theorem orderBatch02 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 2 j)) (catalogueK (slot 2 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [155, 209] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1238, 1659] 14 (by decide +kernel)
  · exact productTest_of_orderTest [181, 190] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1282, 2029] 14 (by decide +kernel)
  · exact productTest_of_orderTest [393, 472] 14 (by decide +kernel)
  · exact productTest_of_orderTest [153, 968] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1114, 1583] 14 (by decide +kernel)
  · exact productTest_of_orderTest [150, 197] 14 (by decide +kernel)
  · exact productTest_of_orderTest [102, 961] 14 (by decide +kernel)
  · exact productTest_of_orderTest [81, 1799] 14 (by decide +kernel)
  · exact productTest_of_orderTest [586, 600] 14 (by decide +kernel)
  · exact productTest_of_orderTest [137, 216] 14 (by decide +kernel)
  · exact productTest_of_orderTest [641, 665] 14 (by decide +kernel)
  · exact productTest_of_orderTest [27, 460] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1354, 1844] 14 (by decide +kernel)
  · exact productTest_of_orderTest [16, 845] 14 (by decide +kernel)
  · exact productTest_of_orderTest [278, 938] 14 (by decide +kernel)
  · exact productTest_of_orderTest [1236, 1272] 14 (by decide +kernel)
  · exact productTest_of_orderTest [870, 893] 14 (by decide +kernel)
  · exact productTest_of_orderTest [72, 968] 14 (by decide +kernel)
  · exact productTest_of_orderTest [174, 228] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1158, 1228] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1438, 1492] 3 (by decide +kernel)
  · exact productTest_of_orderTest [642, 712] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1061, 1135] 3 (by decide +kernel)
  · exact productTest_of_orderTest [524, 582] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1391, 1454] 3 (by decide +kernel)
  · exact productTest_of_orderTest [788, 990] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1243, 1791] 3 (by decide +kernel)
  · exact productTest_of_orderTest [517, 670] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1145, 1187] 3 (by decide +kernel)
  · exact productTest_of_orderTest [222, 727] 3 (by decide +kernel)

theorem orderBatch03 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 3 j)) (catalogueK (slot 3 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1171, 1539] 3 (by decide +kernel)
  · exact productTest_of_orderTest [308, 813] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1821, 2007] 3 (by decide +kernel)
  · exact productTest_of_orderTest [371, 926] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1803, 1875] 3 (by decide +kernel)
  · exact productTest_of_orderTest [403, 473] 3 (by decide +kernel)
  · exact productTest_of_orderTest [374, 978] 3 (by decide +kernel)
  · exact productTest_of_orderTest [931, 954] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1272, 1761] 3 (by decide +kernel)
  · exact productTest_of_orderTest [346, 932] 3 (by decide +kernel)
  · exact productTest_of_orderTest [551, 700] 3 (by decide +kernel)
  · exact productTest_of_orderTest [233, 1003] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1114, 1664] 3 (by decide +kernel)
  · exact productTest_of_orderTest [202, 1024] 3 (by decide +kernel)
  · exact productTest_of_orderTest [744, 1108] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1069, 1597] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1640, 1641] 3 (by decide +kernel)
  · exact productTest_of_orderTest [745, 1118] 3 (by decide +kernel)
  · exact productTest_of_orderTest [254, 705] 3 (by decide +kernel)
  · exact productTest_of_orderTest [410, 1434] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1141, 1483] 3 (by decide +kernel)
  · exact productTest_of_orderTest [476, 860] 3 (by decide +kernel)
  · exact productTest_of_orderTest [55, 704] 3 (by decide +kernel)
  · exact productTest_of_orderTest [56, 168] 3 (by decide +kernel)
  · exact productTest_of_orderTest [57, 930] 3 (by decide +kernel)
  · exact productTest_of_orderTest [430, 892] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1487, 1907] 3 (by decide +kernel)
  · exact productTest_of_orderTest [320, 778] 3 (by decide +kernel)
  · exact productTest_of_orderTest [57, 633] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1453, 1980] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1597, 1899] 3 (by decide +kernel)
  · exact productTest_of_orderTest [20, 799] 3 (by decide +kernel)

theorem orderBatch04 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 4 j)) (catalogueK (slot 4 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1679, 1971] 3 (by decide +kernel)
  · exact productTest_of_orderTest [490, 592] 3 (by decide +kernel)
  · exact productTest_of_orderTest [680, 1622] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1636, 2002] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1265, 1469] 3 (by decide +kernel)
  · exact productTest_of_orderTest [620, 1063] 3 (by decide +kernel)
  · exact productTest_of_orderTest [276, 966] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1350, 1692] 3 (by decide +kernel)
  · exact productTest_of_orderTest [508, 961] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1427, 1553] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1159, 1315] 3 (by decide +kernel)
  · exact productTest_of_orderTest [1201, 1210] 4 (by decide +kernel)
  · exact productTest_of_orderTest [274, 344] 4 (by decide +kernel)
  · exact productTest_of_orderTest [277, 351] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1424, 1435] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1625, 1737] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1803, 2010] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1110, 1238] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1848, 1971] 4 (by decide +kernel)
  · exact productTest_of_orderTest [559, 613] 4 (by decide +kernel)
  · exact productTest_of_orderTest [224, 604] 4 (by decide +kernel)
  · exact productTest_of_orderTest [455, 990] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1860, 1934] 4 (by decide +kernel)
  · exact productTest_of_orderTest [714, 728] 4 (by decide +kernel)
  · exact productTest_of_orderTest [313, 816] 4 (by decide +kernel)
  · exact productTest_of_orderTest [345, 392] 4 (by decide +kernel)
  · exact productTest_of_orderTest [429, 485] 4 (by decide +kernel)
  · exact productTest_of_orderTest [91, 549] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1556, 1693] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1573, 1574] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1340, 1399] 4 (by decide +kernel)
  · exact productTest_of_orderTest [249, 745] 4 (by decide +kernel)

theorem orderBatch05 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 5 j)) (catalogueK (slot 5 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1040, 1051] 4 (by decide +kernel)
  · exact productTest_of_orderTest [239, 253] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1656, 1714] 4 (by decide +kernel)
  · exact productTest_of_orderTest [930, 993] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1491, 2044] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1342, 1451] 4 (by decide +kernel)
  · exact productTest_of_orderTest [305, 783] 4 (by decide +kernel)
  · exact productTest_of_orderTest [59, 683] 4 (by decide +kernel)
  · exact productTest_of_orderTest [87, 2031] 4 (by decide +kernel)
  · exact productTest_of_orderTest [14, 652] 4 (by decide +kernel)
  · exact productTest_of_orderTest [185, 607] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1823, 1887] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1678, 1695] 4 (by decide +kernel)
  · exact productTest_of_orderTest [869, 1022] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1528, 1832] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1171, 1743] 4 (by decide +kernel)
  · exact productTest_of_orderTest [82, 449] 4 (by decide +kernel)
  · exact productTest_of_orderTest [324, 684] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1026, 1178] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1301, 1773] 4 (by decide +kernel)
  · exact productTest_of_orderTest [741, 1637] 4 (by decide +kernel)
  · exact productTest_of_orderTest [52, 792] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1824, 1960] 4 (by decide +kernel)
  · exact productTest_of_orderTest [246, 751] 4 (by decide +kernel)
  · exact productTest_of_orderTest [308, 1604] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1140, 1927] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1422, 1870] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1389, 1958] 4 (by decide +kernel)
  · exact productTest_of_orderTest [958, 1648] 4 (by decide +kernel)
  · exact productTest_of_orderTest [142, 1800] 4 (by decide +kernel)
  · exact productTest_of_orderTest [1655, 1850] 4 (by decide +kernel)
  · exact productTest_of_orderTest [837, 1227] 4 (by decide +kernel)

theorem orderBatch06 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 6 j)) (catalogueK (slot 6 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1338, 1821] 7 (by decide +kernel)
  · exact productTest_of_orderTest [504, 917] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1145, 1695] 7 (by decide +kernel)
  · exact productTest_of_orderTest [41, 708] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1419, 2046] 7 (by decide +kernel)
  · exact productTest_of_orderTest [322, 893] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1458, 1950] 7 (by decide +kernel)
  · exact productTest_of_orderTest [203, 574] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1281, 1344] 7 (by decide +kernel)
  · exact productTest_of_orderTest [482, 965] 7 (by decide +kernel)
  · exact productTest_of_orderTest [588, 653] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1339, 1440] 7 (by decide +kernel)
  · exact productTest_of_orderTest [427, 481] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1949, 2007] 7 (by decide +kernel)
  · exact productTest_of_orderTest [48, 726] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1081, 1211] 7 (by decide +kernel)
  · exact productTest_of_orderTest [272, 337] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1112, 1772] 7 (by decide +kernel)
  · exact productTest_of_orderTest [846, 916] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1565, 1628] 7 (by decide +kernel)
  · exact productTest_of_orderTest [185, 227] 7 (by decide +kernel)
  · exact productTest_of_orderTest [128, 193] 7 (by decide +kernel)
  · exact productTest_of_orderTest [411, 997] 7 (by decide +kernel)
  · exact productTest_of_orderTest [919, 935] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1820, 1932] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1297, 1434] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1765, 1791] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1160, 1219] 7 (by decide +kernel)
  · exact productTest_of_orderTest [702, 740] 7 (by decide +kernel)
  · exact productTest_of_orderTest [424, 483] 7 (by decide +kernel)
  · exact productTest_of_orderTest [524, 582] 7 (by decide +kernel)
  · exact productTest_of_orderTest [82, 1331] 7 (by decide +kernel)

theorem orderBatch07 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 7 j)) (catalogueK (slot 7 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1853, 1941] 7 (by decide +kernel)
  · exact productTest_of_orderTest [368, 854] 7 (by decide +kernel)
  · exact productTest_of_orderTest [467, 1830] 7 (by decide +kernel)
  · exact productTest_of_orderTest [1274, 1908] 7 (by decide +kernel)
  · exact productTest_of_orderTest [352, 790] 7 (by decide +kernel)
  · exact productTest_of_orderTest [136, 556] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1399, 1922] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1179, 1572] 8 (by decide +kernel)
  · exact productTest_of_orderTest [293, 897] 8 (by decide +kernel)
  · exact productTest_of_orderTest [424, 927] 8 (by decide +kernel)
  · exact productTest_of_orderTest [373, 896] 8 (by decide +kernel)
  · exact productTest_of_orderTest [9, 759] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1229, 1707] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1253, 1552] 8 (by decide +kernel)
  · exact productTest_of_orderTest [34, 526] 8 (by decide +kernel)
  · exact productTest_of_orderTest [504, 917] 8 (by decide +kernel)
  · exact productTest_of_orderTest [358, 899] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1815, 1878] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1282, 2028] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1801, 1992] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1076, 1150] 8 (by decide +kernel)
  · exact productTest_of_orderTest [775, 924] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1408, 1482] 8 (by decide +kernel)
  · exact productTest_of_orderTest [629, 710] 8 (by decide +kernel)
  · exact productTest_of_orderTest [773, 858] 8 (by decide +kernel)
  · exact productTest_of_orderTest [589, 605] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1561, 1788] 8 (by decide +kernel)
  · exact productTest_of_orderTest [201, 211] 8 (by decide +kernel)
  · exact productTest_of_orderTest [162, 708] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1826, 1851] 8 (by decide +kernel)
  · exact productTest_of_orderTest [380, 435] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1415, 1889] 8 (by decide +kernel)

theorem orderBatch08 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 8 j)) (catalogueK (slot 8 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [985, 1108] 8 (by decide +kernel)
  · exact productTest_of_orderTest [56, 186] 8 (by decide +kernel)
  · exact productTest_of_orderTest [564, 676] 8 (by decide +kernel)
  · exact productTest_of_orderTest [19, 1954] 8 (by decide +kernel)
  · exact productTest_of_orderTest [548, 1530] 8 (by decide +kernel)
  · exact productTest_of_orderTest [840, 856] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1287, 1692] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1301, 1734] 8 (by decide +kernel)
  · exact productTest_of_orderTest [590, 732] 8 (by decide +kernel)
  · exact productTest_of_orderTest [64, 1961] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1258, 1388] 8 (by decide +kernel)
  · exact productTest_of_orderTest [319, 506] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1125, 1900] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1231, 1615] 8 (by decide +kernel)
  · exact productTest_of_orderTest [922, 1642] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1146, 1763] 8 (by decide +kernel)
  · exact productTest_of_orderTest [1177, 1240] 9 (by decide +kernel)
  · exact productTest_of_orderTest [100, 127] 9 (by decide +kernel)
  · exact productTest_of_orderTest [658, 712] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1536, 1626] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1077, 1135] 9 (by decide +kernel)
  · exact productTest_of_orderTest [137, 200] 9 (by decide +kernel)
  · exact productTest_of_orderTest [152, 194] 9 (by decide +kernel)
  · exact productTest_of_orderTest [260, 325] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1169, 1227] 9 (by decide +kernel)
  · exact productTest_of_orderTest [418, 483] 9 (by decide +kernel)
  · exact productTest_of_orderTest [97, 171] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1054, 1157] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1838, 2047] 9 (by decide +kernel)
  · exact productTest_of_orderTest [586, 593] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1347, 1496] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1465, 1507] 9 (by decide +kernel)

theorem orderBatch09 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 9 j)) (catalogueK (slot 9 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [521, 530] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1034, 1041] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1056, 1195] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1155, 1176] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1558, 1670] 9 (by decide +kernel)
  · exact productTest_of_orderTest [72, 83] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1092, 1108] 9 (by decide +kernel)
  · exact productTest_of_orderTest [228, 1124] 9 (by decide +kernel)
  · exact productTest_of_orderTest [294, 508] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1049, 1608] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1843, 1971] 9 (by decide +kernel)
  · exact productTest_of_orderTest [84, 207] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1091, 1179] 9 (by decide +kernel)
  · exact productTest_of_orderTest [444, 998] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1158, 1776] 9 (by decide +kernel)
  · exact productTest_of_orderTest [26, 64] 9 (by decide +kernel)
  · exact productTest_of_orderTest [161, 225] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1446, 1958] 9 (by decide +kernel)
  · exact productTest_of_orderTest [807, 886] 9 (by decide +kernel)
  · exact productTest_of_orderTest [559, 608] 9 (by decide +kernel)
  · exact productTest_of_orderTest [316, 323] 9 (by decide +kernel)
  · exact productTest_of_orderTest [529, 1690] 9 (by decide +kernel)
  · exact productTest_of_orderTest [583, 1981] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1121, 1129] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1405, 2036] 9 (by decide +kernel)
  · exact productTest_of_orderTest [19, 21] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1816, 1881] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1196, 1215] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1306, 1973] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1213, 1230] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1042, 1745] 9 (by decide +kernel)
  · exact productTest_of_orderTest [144, 444] 9 (by decide +kernel)

theorem orderBatch10 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 10 j)) (catalogueK (slot 10 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1091, 1198] 9 (by decide +kernel)
  · exact productTest_of_orderTest [274, 364] 9 (by decide +kernel)
  · exact productTest_of_orderTest [246, 567] 9 (by decide +kernel)
  · exact productTest_of_orderTest [1162, 1598] 9 (by decide +kernel)
  · exact productTest_of_orderTest [34, 238] 9 (by decide +kernel)
  · exact productTest_of_orderTest [534, 604] 10 (by decide +kernel)
  · exact productTest_of_orderTest [642, 658] 10 (by decide +kernel)
  · exact productTest_of_orderTest [647, 717] 10 (by decide +kernel)
  · exact productTest_of_orderTest [520, 578] 10 (by decide +kernel)
  · exact productTest_of_orderTest [742, 758] 10 (by decide +kernel)
  · exact productTest_of_orderTest [553, 562] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1827, 1897] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1211, 1265] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1433, 1496] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1544, 1609] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1585, 1648] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1442, 1976] 10 (by decide +kernel)
  · exact productTest_of_orderTest [681, 754] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1242, 1675] 10 (by decide +kernel)
  · exact productTest_of_orderTest [609, 619] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1874, 1881] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1514, 1969] 10 (by decide +kernel)
  · exact productTest_of_orderTest [82, 1224] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1600, 1704] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1121, 1266] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1490, 1513] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1090, 1416] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1379, 1568] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1832, 2034] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1311, 1364] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1026, 1226] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1539, 1672] 10 (by decide +kernel)

theorem orderBatch11 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 11 j)) (catalogueK (slot 11 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1289, 1417] 10 (by decide +kernel)
  · exact productTest_of_orderTest [390, 396] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1345, 1537] 10 (by decide +kernel)
  · exact productTest_of_orderTest [269, 798] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1170, 1176] 10 (by decide +kernel)
  · exact productTest_of_orderTest [300, 1005] 10 (by decide +kernel)
  · exact productTest_of_orderTest [678, 700] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1171, 1666] 10 (by decide +kernel)
  · exact productTest_of_orderTest [710, 732] 10 (by decide +kernel)
  · exact productTest_of_orderTest [322, 776] 10 (by decide +kernel)
  · exact productTest_of_orderTest [1555, 1618] 10 (by decide +kernel)
  · exact productTest_of_orderTest [80, 1954] 10 (by decide +kernel)
  · exact productTest_of_orderTest [349, 565] 10 (by decide +kernel)
  · exact productTest_of_orderTest [679, 684] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1320, 1378] 5 (by decide +kernel)
  · exact productTest_of_orderTest [261, 286] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1087, 1141] 5 (by decide +kernel)
  · exact productTest_of_orderTest [642, 658] 5 (by decide +kernel)
  · exact productTest_of_orderTest [289, 363] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1415, 1501] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1232, 1243] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1285, 1294] 5 (by decide +kernel)
  · exact productTest_of_orderTest [667, 714] 5 (by decide +kernel)
  · exact productTest_of_orderTest [377, 862] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1106, 1766] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1369, 1917] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1370, 1909] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1265, 1548] 5 (by decide +kernel)
  · exact productTest_of_orderTest [186, 224] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1445, 1818] 5 (by decide +kernel)
  · exact productTest_of_orderTest [428, 850] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1128, 1748] 5 (by decide +kernel)

theorem orderBatch12 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 12 j)) (catalogueK (slot 12 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1450, 2007] 5 (by decide +kernel)
  · exact productTest_of_orderTest [324, 883] 5 (by decide +kernel)
  · exact productTest_of_orderTest [124, 723] 5 (by decide +kernel)
  · exact productTest_of_orderTest [383, 407] 5 (by decide +kernel)
  · exact productTest_of_orderTest [86, 552] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1287, 1851] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1241, 1721] 5 (by decide +kernel)
  · exact productTest_of_orderTest [208, 639] 5 (by decide +kernel)
  · exact productTest_of_orderTest [815, 831] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1023, 2047] 5 (by decide +kernel)
  · exact productTest_of_orderTest [820, 896] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1062, 1085] 5 (by decide +kernel)
  · exact productTest_of_orderTest [510, 1381] 5 (by decide +kernel)
  · exact productTest_of_orderTest [783, 837] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1375, 1912] 5 (by decide +kernel)
  · exact productTest_of_orderTest [92, 161] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1425, 1471] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1093, 1769] 5 (by decide +kernel)
  · exact productTest_of_orderTest [681, 1029] 5 (by decide +kernel)
  · exact productTest_of_orderTest [1574, 1639] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1082, 1147] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1821, 1884] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1209, 1272] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1562, 1627] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1587, 1650] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1301, 1364] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1180, 1245] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1340, 1405] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1079, 1142] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1951, 2014] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1290, 1355] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1931, 1994] 6 (by decide +kernel)

theorem orderBatch13 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 13 j)) (catalogueK (slot 13 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [1830, 1895] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1662, 1711] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1357, 1431] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1190, 1255] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1975, 2038] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1458, 1523] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1719, 1782] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1978, 2043] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1844, 1909] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1794, 1938] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1818, 1883] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1303, 1963] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1188, 1691] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1265, 1543] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1187, 1733] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1484, 1904] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1182, 1779] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1330, 1934] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1091, 1660] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1407, 1856] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1376, 1868] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1183, 1715] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1296, 1893] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1810, 1947] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1171, 1708] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1353, 1910] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1667, 1681] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1685, 1713] 6 (by decide +kernel)
  · exact productTest_of_orderTest [1283, 1900] 13 (by decide +kernel)
  · exact productTest_of_orderTest [1686, 1787] 13 (by decide +kernel)
  · exact productTest_of_orderTest [415, 1718] 13 (by decide +kernel)
  · exact productTest_of_orderTest [344, 1264] 13 (by decide +kernel)

theorem orderBatch14 : ∀ j : Fin 32,
    productTest (catalogueNs (slot 14 j)) (catalogueK (slot 14 j)) = true := by
  intro j
  fin_cases j
  · exact productTest_of_orderTest [916, 1835] 13 (by decide +kernel)
  · exact productTest_of_orderTest [925, 1322] 13 (by decide +kernel)
  · exact productTest_of_orderTest [65, 1925] 13 (by decide +kernel)
  · exact productTest_of_orderTest [519, 1622] 13 (by decide +kernel)
  · exact productTest_of_orderTest [805, 1174] 13 (by decide +kernel)
  · exact productTest_of_orderTest [705, 1700] 13 (by decide +kernel)
  · exact productTest_of_orderTest [1510, 1651] 13 (by decide +kernel)
  · exact productTest_of_orderTest [1071, 1681] 16 (by decide +kernel)
  · exact productTest_of_orderTest [1840, 1951] 16 (by decide +kernel)
  · exact productTest_of_orderTest [1410, 1496] 16 (by decide +kernel)
  · exact productTest_of_orderTest [349, 1547] 16 (by decide +kernel)
  · exact productTest_of_orderTest [875, 2032] 16 (by decide +kernel)
  · exact productTest_of_orderTest [187, 710] 16 (by decide +kernel)
  · exact productTest_of_orderTest [1395, 1528] 16 (by decide +kernel)
  · exact productTest_of_orderTest [159, 169] 16 (by decide +kernel)
  · exact productTest_of_orderTest [655, 732] 16 (by decide +kernel)
  · exact productTest_of_orderTest [1591, 1942] 16 (by decide +kernel)
  · exact productTest_of_orderTest [314, 442] 15 (by decide +kernel)
  · exact productTest_of_orderTest [888, 1276] 15 (by decide +kernel)
  · exact productTest_of_orderTest [1171, 1420] 15 (by decide +kernel)
  · exact productTest_of_orderTest [598, 646] 15 (by decide +kernel)
  · exact productTest_of_orderTest [245, 1703] 15 (by decide +kernel)
  · exact productTest_of_orderTest [844, 972] 17 (by decide +kernel)
  · exact productTest_of_orderTest [540, 718] 17 (by decide +kernel)
  · exact productTest_of_orderTest [252, 1016] 17 (by decide +kernel)
  · exact productTest_of_orderTest [245, 370] 17 (by decide +kernel)
  · exact productTest_of_orderTest [1278, 1907] 17 (by decide +kernel)
  · exact productTest_of_orderTest [1738, 1754] 11 (by decide +kernel)
  · exact productTest_of_orderTest [884, 940] 11 (by decide +kernel)
  · exact productTest_of_orderTest [1419, 1498] 11 (by decide +kernel)
  · exact productTest_of_orderTest [118, 181] 11 (by decide +kernel)
  · exact productTest_of_orderTest [768, 842] 11 (by decide +kernel)

theorem catalogueCorrect (r : Fin 475) :
    productTest (catalogueNs r) (catalogueK r) = true := by
  have h : ∀ b : Fin 15, ∀ j : Fin 32,
      productTest (catalogueNs (slot b j)) (catalogueK (slot b j)) = true := by
    intro b
    fin_cases b
    · exact orderBatch00
    · exact orderBatch01
    · exact orderBatch02
    · exact orderBatch03
    · exact orderBatch04
    · exact orderBatch05
    · exact orderBatch06
    · exact orderBatch07
    · exact orderBatch08
    · exact orderBatch09
    · exact orderBatch10
    · exact orderBatch11
    · exact orderBatch12
    · exact orderBatch13
    · exact orderBatch14
  let b : Fin 15 := ⟨r.val / 32, by omega⟩
  let j : Fin 32 := ⟨r.val % 32, Nat.mod_lt _ (by decide)⟩
  have hs : slot b j = r := by
    apply Fin.ext
    dsimp [slot, b, j]
    omega
  simpa only [hs] using h b j
end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ProductCertificates
