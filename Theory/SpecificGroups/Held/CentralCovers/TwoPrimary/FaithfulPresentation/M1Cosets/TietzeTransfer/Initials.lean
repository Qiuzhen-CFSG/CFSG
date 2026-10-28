module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.SchreierData

/-!
# Matching the literal replay inputs to the Schreier presentation

Every selected input is checked against the exact shared `initialRelator`,
including the protected-symbol equations, with its original numbering.

Source: John Bray, ATLAS `HeG1-P1.M`; the retained 17-generator trace and
the untrusted producer are documented in `TietzeTransfer/source/README.md`.
-/

@[expose] public section

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Initials
open Replay

open Data Theory.GroupTheory.CosetEnumeration

variable {G : Type*} [Group G] {g : Nat → G}

def Initial {G : Type*} [Group G] (g : Nat → G) : Prop :=
  ∀ r : Fin 14409, eval g (Schreier.initialRelator r) = 1

def indices0 : List (Fin 14409) := [0, 1, 3, 7, 8, 9, 10, 12, 13, 14, 15, 17, 21, 22, 24, 26, 27, 28, 29, 31, 33, 35, 36, 37, 38, 40, 42, 43, 44, 47, 49, 50, 51, 52, 54, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 68, 70, 71, 73, 75, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92]

private theorem checked0 : verifyInputs db Schreier.initialRelator 0 indices0 = true := by decide +kernel

private theorem prefix0 (hi : Initial g) : ValidBefore g db 64 :=
  verifyInputs_sound hi (fun _ h => (Nat.not_lt_zero _ h).elim) indices0 checked0

def indices1 : List (Fin 14409) := [94, 97, 98, 99, 101, 103, 105, 106, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 132, 133, 134, 135, 136, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 154, 155, 157, 159, 161, 162, 164, 168, 169, 171, 174, 175, 176, 177, 178, 180, 182]

private theorem checked1 : verifyInputs db Schreier.initialRelator 64 indices1 = true := by decide +kernel

private theorem prefix1 (hi : Initial g) : ValidBefore g db 128 :=
  verifyInputs_sound hi (prefix0 hi) indices1 checked1

def indices2 : List (Fin 14409) := [183, 185, 189, 191, 192, 194, 195, 196, 197, 198, 199, 203, 204, 206, 208, 210, 211, 212, 213, 215, 217, 218, 219, 220, 222, 224, 225, 227, 230, 231, 236, 238, 239, 240, 241, 244, 245, 246, 247, 248, 250, 252, 253, 254, 255, 257, 258, 260, 265, 266, 269, 271, 273, 274, 276, 278, 279, 280, 281, 283, 287, 288, 289, 290]

private theorem checked2 : verifyInputs db Schreier.initialRelator 128 indices2 = true := by decide +kernel

private theorem prefix2 (hi : Initial g) : ValidBefore g db 192 :=
  verifyInputs_sound hi (prefix1 hi) indices2 checked2

def indices3 : List (Fin 14409) := [294, 295, 296, 297, 299, 300, 301, 302, 304, 308, 309, 311, 313, 315, 316, 318, 319, 320, 321, 322, 323, 325, 328, 329, 332, 336, 337, 339, 341, 343, 344, 346, 348, 350, 351, 352, 356, 357, 358, 360, 362, 364, 371, 372, 373, 378, 381, 385, 386, 388, 389, 391, 392, 393, 395, 398, 399, 400, 405, 406, 409, 411, 413, 414]

private theorem checked3 : verifyInputs db Schreier.initialRelator 192 indices3 = true := by decide +kernel

private theorem prefix3 (hi : Initial g) : ValidBefore g db 256 :=
  verifyInputs_sound hi (prefix2 hi) indices3 checked3

def indices4 : List (Fin 14409) := [415, 416, 418, 419, 420, 421, 422, 425, 426, 427, 428, 430, 433, 434, 435, 437, 439, 440, 441, 442, 444, 446, 448, 449, 451, 455, 462, 463, 465, 467, 468, 469, 470, 471, 472, 474, 475, 476, 477, 479, 481, 483, 484, 486, 488, 490, 491, 492, 493, 495, 496, 497, 498, 500, 504, 505, 507, 511, 512, 513, 518, 519, 520, 521]

private theorem checked4 : verifyInputs db Schreier.initialRelator 256 indices4 = true := by decide +kernel

private theorem prefix4 (hi : Initial g) : ValidBefore g db 320 :=
  verifyInputs_sound hi (prefix3 hi) indices4 checked4

def indices5 : List (Fin 14409) := [525, 526, 527, 528, 531, 532, 533, 535, 539, 540, 541, 542, 545, 546, 547, 549, 553, 554, 556, 560, 561, 563, 566, 567, 568, 569, 573, 574, 575, 577, 581, 584, 586, 588, 589, 590, 593, 595, 596, 598, 602, 603, 605, 607, 608, 609, 610, 611, 612, 614, 616, 617, 619, 623, 624, 625, 626, 628, 630, 635, 637, 640, 643, 644]

private theorem checked5 : verifyInputs db Schreier.initialRelator 320 indices5 = true := by decide +kernel

private theorem prefix5 (hi : Initial g) : ValidBefore g db 384 :=
  verifyInputs_sound hi (prefix4 hi) indices5 checked5

def indices6 : List (Fin 14409) := [647, 651, 652, 658, 659, 661, 665, 666, 672, 673, 675, 677, 678, 679, 680, 681, 682, 684, 686, 687, 693, 694, 696, 698, 700, 701, 702, 703, 705, 706, 707, 710, 712, 715, 716, 721, 726, 727, 728, 729, 730, 731, 734, 735, 738, 742, 743, 744, 745, 747, 749, 756, 757, 759, 761, 763, 764, 766, 768, 769, 770, 773, 777, 780]

private theorem checked6 : verifyInputs db Schreier.initialRelator 384 indices6 = true := by decide +kernel

private theorem prefix6 (hi : Initial g) : ValidBefore g db 448 :=
  verifyInputs_sound hi (prefix5 hi) indices6 checked6

def indices7 : List (Fin 14409) := [783, 784, 785, 787, 790, 791, 792, 794, 797, 798, 799, 800, 801, 803, 806, 811, 813, 819, 822, 824, 825, 827, 828, 834, 840, 841, 842, 843, 847, 848, 849, 850, 853, 854, 855, 857, 859, 862, 863, 868, 871, 875, 878, 882, 883, 885, 889, 890, 892, 895, 896, 897, 901, 903, 910, 913, 916, 917, 920, 924, 925, 927, 931, 932]

private theorem checked7 : verifyInputs db Schreier.initialRelator 448 indices7 = true := by decide +kernel

private theorem prefix7 (hi : Initial g) : ValidBefore g db 512 :=
  verifyInputs_sound hi (prefix6 hi) indices7 checked7

def indices8 : List (Fin 14409) := [934, 936, 938, 941, 945, 947, 950, 951, 952, 953, 954, 957, 959, 962, 966, 967, 969, 971, 972, 973, 974, 976, 980, 981, 983, 985, 986, 987, 988, 993, 994, 1001, 1002, 1004, 1008, 1011, 1013, 1022, 1023, 1024, 1025, 1027, 1028, 1029, 1030, 1031, 1032, 1034, 1035, 1036, 1042, 1043, 1044, 1046, 1050, 1051, 1053, 1055, 1058, 1063, 1064, 1067, 1070, 1071]

private theorem checked8 : verifyInputs db Schreier.initialRelator 512 indices8 = true := by decide +kernel

private theorem prefix8 (hi : Initial g) : ValidBefore g db 576 :=
  verifyInputs_sound hi (prefix7 hi) indices8 checked8

def indices9 : List (Fin 14409) := [1072, 1074, 1078, 1079, 1083, 1085, 1086, 1088, 1090, 1091, 1092, 1099, 1100, 1106, 1107, 1109, 1113, 1116, 1120, 1121, 1122, 1123, 1127, 1128, 1129, 1130, 1132, 1134, 1135, 1136, 1137, 1141, 1142, 1144, 1148, 1149, 1151, 1153, 1155, 1158, 1160, 1161, 1162, 1165, 1167, 1168, 1169, 1170, 1172, 1176, 1177, 1179, 1181, 1183, 1184, 1186, 1189, 1190, 1191, 1193, 1196, 1197, 1200, 1203]

private theorem checked9 : verifyInputs db Schreier.initialRelator 576 indices9 = true := by decide +kernel

private theorem prefix9 (hi : Initial g) : ValidBefore g db 640 :=
  verifyInputs_sound hi (prefix8 hi) indices9 checked9

def indices10 : List (Fin 14409) := [1204, 1209, 1210, 1211, 1214, 1216, 1218, 1219, 1221, 1225, 1228, 1232, 1235, 1239, 1240, 1242, 1244, 1245, 1246, 1249, 1251, 1252, 1254, 1260, 1263, 1267, 1268, 1269, 1270, 1273, 1274, 1277, 1281, 1284, 1287, 1288, 1291, 1295, 1296, 1297, 1298, 1301, 1302, 1303, 1305, 1309, 1310, 1311, 1312, 1315, 1316, 1319, 1321, 1322, 1323, 1324, 1326, 1328, 1329, 1330, 1332, 1333, 1336, 1337]

private theorem checked10 : verifyInputs db Schreier.initialRelator 640 indices10 = true := by decide +kernel

private theorem prefix10 (hi : Initial g) : ValidBefore g db 704 :=
  verifyInputs_sound hi (prefix9 hi) indices10 checked10

def indices11 : List (Fin 14409) := [1340, 1343, 1344, 1345, 1346, 1347, 1350, 1351, 1352, 1354, 1357, 1359, 1365, 1366, 1368, 1370, 1371, 1372, 1375, 1379, 1382, 1384, 1386, 1389, 1392, 1393, 1394, 1396, 1398, 1400, 1401, 1403, 1405, 1407, 1408, 1412, 1414, 1415, 1416, 1417, 1421, 1422, 1424, 1428, 1429, 1431, 1435, 1437, 1438, 1440, 1441, 1442, 1443, 1444, 1445, 1447, 1448, 1449, 1452, 1454, 1455, 1456, 1457, 1458]

private theorem checked11 : verifyInputs db Schreier.initialRelator 704 indices11 = true := by decide +kernel

private theorem prefix11 (hi : Initial g) : ValidBefore g db 768 :=
  verifyInputs_sound hi (prefix10 hi) indices11 checked11

def indices12 : List (Fin 14409) := [1459, 1463, 1464, 1466, 1470, 1471, 1473, 1475, 1478, 1484, 1485, 1487, 1489, 1490, 1491, 1492, 1494, 1498, 1501, 1503, 1504, 1505, 1506, 1508, 1510, 1512, 1515, 1519, 1520, 1522, 1533, 1534, 1536, 1540, 1542, 1543, 1547, 1550, 1553, 1554, 1557, 1558, 1559, 1560, 1561, 1563, 1564, 1566, 1568, 1575, 1578, 1580, 1582, 1583, 1588, 1589, 1592, 1596, 1599, 1603, 1606, 1609, 1610, 1613]

private theorem checked12 : verifyInputs db Schreier.initialRelator 768 indices12 = true := by decide +kernel

private theorem prefix12 (hi : Initial g) : ValidBefore g db 832 :=
  verifyInputs_sound hi (prefix11 hi) indices12 checked12

def indices13 : List (Fin 14409) := [1618, 1623, 1624, 1625, 1627, 1629, 1630, 1631, 1633, 1634, 1636, 1638, 1639, 1641, 1643, 1647, 1651, 1652, 1655, 1657, 1658, 1659, 1660, 1662, 1666, 1669, 1671, 1673, 1674, 1680, 1681, 1686, 1687, 1688, 1690, 1694, 1697, 1700, 1701, 1706, 1707, 1708, 1711, 1714, 1715, 1720, 1722, 1723, 1728, 1729, 1732, 1736, 1739, 1743, 1748, 1750, 1751, 1753, 1757, 1758, 1760, 1762, 1764, 1771]

private theorem checked13 : verifyInputs db Schreier.initialRelator 832 indices13 = true := by decide +kernel

private theorem prefix13 (hi : Initial g) : ValidBefore g db 896 :=
  verifyInputs_sound hi (prefix12 hi) indices13 checked13

def indices14 : List (Fin 14409) := [1774, 1778, 1781, 1783, 1784, 1785, 1786, 1788, 1792, 1795, 1798, 1799, 1802, 1806, 1807, 1809, 1812, 1813, 1814, 1816, 1818, 1819, 1820, 1823, 1825, 1827, 1830, 1832, 1834, 1837, 1840, 1841, 1844, 1848, 1851, 1855, 1856, 1858, 1862, 1867, 1869, 1870, 1872, 1876, 1879, 1882, 1883, 1886, 1888, 1890, 1893, 1896, 1903, 1904, 1911, 1914, 1918, 1921, 1925, 1928, 1931, 1932, 1935, 1937]

private theorem checked14 : verifyInputs db Schreier.initialRelator 896 indices14 = true := by decide +kernel

private theorem prefix14 (hi : Initial g) : ValidBefore g db 960 :=
  verifyInputs_sound hi (prefix13 hi) indices14 checked14

def indices15 : List (Fin 14409) := [1939, 1940, 1942, 1944, 1945, 1946, 1947, 1949, 1953, 1954, 1956, 1959, 1960, 1963, 1965, 1966, 1967, 1970, 1973, 1974, 1976, 1977, 1981, 1984, 1989, 1990, 1994, 1995, 1998, 2002, 2005, 2007, 2015, 2016, 2017, 2019, 2022, 2023, 2024, 2026, 2029, 2036, 2037, 2038, 2040, 2043, 2044, 2047, 2051, 2054, 2058, 2059, 2061, 2062, 2064, 2065, 2066, 2068, 2072, 2073, 2075, 2078, 2079, 2082]

private theorem checked15 : verifyInputs db Schreier.initialRelator 960 indices15 = true := by decide +kernel

private theorem prefix15 (hi : Initial g) : ValidBefore g db 1024 :=
  verifyInputs_sound hi (prefix14 hi) indices15 checked15

def indices16 : List (Fin 14409) := [2086, 2089, 2091, 2093, 2094, 2096, 2099, 2100, 2103, 2105, 2107, 2110, 2114, 2117, 2119, 2121, 2122, 2124, 2126, 2127, 2128, 2131, 2142, 2145, 2147, 2148, 2155, 2156, 2159, 2162, 2163, 2166, 2171, 2177, 2180, 2183, 2184, 2185, 2186, 2187, 2190, 2191, 2194, 2198, 2201, 2205, 2208, 2212, 2215, 2225, 2226, 2227, 2229, 2231, 2233, 2234, 2236, 2238, 2240, 2241, 2243, 2247, 2250, 2254]

private theorem checked16 : verifyInputs db Schreier.initialRelator 1024 indices16 = true := by decide +kernel

private theorem prefix16 (hi : Initial g) : ValidBefore g db 1088 :=
  verifyInputs_sound hi (prefix15 hi) indices16 checked16

def indices17 : List (Fin 14409) := [2257, 2259, 2261, 2264, 2268, 2269, 2274, 2275, 2278, 2282, 2289, 2296, 2302, 2303, 2306, 2310, 2313, 2315, 2316, 2318, 2324, 2330, 2331, 2334, 2335, 2338, 2339, 2341, 2342, 2345, 2348, 2350, 2352, 2355, 2358, 2359, 2360, 2372, 2373, 2376, 2379, 2380, 2383, 2386, 2387, 2390, 2394, 2395, 2397, 2400, 2401, 2404, 2407, 2408, 2409, 2411, 2415, 2418, 2422, 2423, 2425, 2428, 2429, 2432]

private theorem checked17 : verifyInputs db Schreier.initialRelator 1088 indices17 = true := by decide +kernel

private theorem prefix17 (hi : Initial g) : ValidBefore g db 1152 :=
  verifyInputs_sound hi (prefix16 hi) indices17 checked17

def indices18 : List (Fin 14409) := [2436, 2439, 2442, 2443, 2446, 2449, 2450, 2453, 2457, 2464, 2467, 2471, 2474, 2476, 2478, 2479, 2481, 2485, 2488, 2490, 2492, 2493, 2495, 2499, 2500, 2502, 2505, 2506, 2509, 2512, 2513, 2516, 2520, 2523, 2527, 2528, 2530, 2533, 2541, 2544, 2545, 2548, 2551, 2555, 2556, 2562, 2565, 2567, 2568, 2569, 2570, 2572, 2576, 2577, 2579, 2581, 2582, 2583, 2584, 2586, 2589, 2590, 2593, 2596]

private theorem checked18 : verifyInputs db Schreier.initialRelator 1152 indices18 = true := by decide +kernel

private theorem prefix18 (hi : Initial g) : ValidBefore g db 1216 :=
  verifyInputs_sound hi (prefix17 hi) indices18 checked18

def indices19 : List (Fin 14409) := [2597, 2600, 2603, 2610, 2618, 2621, 2625, 2628, 2632, 2635, 2638, 2639, 2642, 2645, 2646, 2649, 2653, 2660, 2663, 2667, 2668, 2674, 2675, 2677, 2680, 2681, 2684, 2688, 2691, 2695, 2696, 2700, 2703, 2708, 2709, 2712, 2714, 2715, 2716, 2719, 2723, 2724, 2726, 2730, 2731, 2733, 2737, 2738, 2740, 2744, 2750, 2751, 2754, 2756, 2757, 2758, 2761, 2764, 2765, 2768, 2770, 2772, 2777, 2780]

private theorem checked19 : verifyInputs db Schreier.initialRelator 1216 indices19 = true := by decide +kernel

private theorem prefix19 (hi : Initial g) : ValidBefore g db 1280 :=
  verifyInputs_sound hi (prefix18 hi) indices19 checked19

def indices20 : List (Fin 14409) := [2792, 2793, 2796, 2799, 2807, 2808, 2810, 2814, 2815, 2817, 2827, 2828, 2834, 2849, 2850, 2852, 2869, 2870, 2873, 2876, 2883, 2884, 2887, 2890, 2891, 2894, 2897, 2898, 2901, 2904, 2905, 2906, 2908, 2910, 2911, 2912, 2919, 2920, 2922, 2926, 2929, 2933, 2936, 2938, 2940, 2943, 2947, 2953, 2954, 2957, 2960, 2962, 2975, 2978, 2980, 2981, 2989, 2992, 2996, 2997, 2999, 3003, 3006, 3009]

private theorem checked20 : verifyInputs db Schreier.initialRelator 1280 indices20 = true := by decide +kernel

private theorem prefix20 (hi : Initial g) : ValidBefore g db 1344 :=
  verifyInputs_sound hi (prefix19 hi) indices20 checked20

def indices21 : List (Fin 14409) := [3010, 3013, 3017, 3020, 3023, 3024, 3027, 3038, 3041, 3044, 3045, 3048, 3052, 3055, 3058, 3059, 3062, 3066, 3067, 3069, 3073, 3076, 3080, 3083, 3087, 3090, 3092, 3094, 3095, 3097, 3100, 3102, 3108, 3111, 3123, 3128, 3129, 3132, 3135, 3136, 3143, 3146, 3157, 3162, 3163, 3164, 3165, 3167, 3169, 3171, 3178, 3181, 3185, 3186, 3188, 3193, 3199, 3206, 3209, 3213, 3216, 3220, 3223, 3227]

private theorem checked21 : verifyInputs db Schreier.initialRelator 1344 indices21 = true := by decide +kernel

private theorem prefix21 (hi : Initial g) : ValidBefore g db 1408 :=
  verifyInputs_sound hi (prefix20 hi) indices21 checked21

def indices22 : List (Fin 14409) := [3230, 3234, 3237, 3241, 3244, 3248, 3251, 3254, 3255, 3258, 3262, 3265, 3269, 3272, 3276, 3279, 3282, 3290, 3293, 3297, 3300, 3318, 3321, 3332, 3333, 3335, 3339, 3346, 3359, 3360, 3361, 3363, 3365, 3366, 3367, 3370, 3373, 3374, 3375, 3377, 3381, 3387, 3394, 3395, 3398, 3401, 3410, 3416, 3419, 3430, 3431, 3433, 3437, 3440, 3444, 3447, 3450, 3458, 3461, 3465, 3468, 3471, 3472, 3475]

private theorem checked22 : verifyInputs db Schreier.initialRelator 1408 indices22 = true := by decide +kernel

private theorem prefix22 (hi : Initial g) : ValidBefore g db 1472 :=
  verifyInputs_sound hi (prefix21 hi) indices22 checked22

def indices23 : List (Fin 14409) := [3479, 3482, 3487, 3492, 3493, 3496, 3500, 3503, 3507, 3510, 3514, 3517, 3520, 3521, 3524, 3528, 3531, 3535, 3538, 3542, 3545, 3549, 3552, 3555, 3569, 3570, 3573, 3577, 3584, 3587, 3589, 3591, 3594, 3599, 3604, 3605, 3608, 3612, 3617, 3619, 3622, 3626, 3629, 3633, 3634, 3636, 3640, 3643, 3647, 3648, 3650, 3654, 3661, 3662, 3674, 3675, 3678, 3689, 3692, 3696, 3699, 3702, 3703, 3706]

private theorem checked23 : verifyInputs db Schreier.initialRelator 1472 indices23 = true := by decide +kernel

private theorem prefix23 (hi : Initial g) : ValidBefore g db 1536 :=
  verifyInputs_sound hi (prefix22 hi) indices23 checked23

def indices24 : List (Fin 14409) := [3710, 3711, 3713, 3717, 3720, 3723, 3724, 3725, 3727, 3733, 3737, 3738, 3739, 3741, 3744, 3745, 3748, 3751, 3759, 3762, 3764, 3772, 3773, 3774, 3776, 3780, 3781, 3783, 3786, 3787, 3790, 3793, 3794, 3797, 3799, 3800, 3801, 3804, 3807, 3808, 3811, 3814, 3815, 3818, 3822, 3825, 3828, 3829, 3832, 3836, 3839, 3842, 3849, 3851, 3877, 3878, 3881, 3884, 3885, 3888, 3891, 3898, 3899, 3904]

private theorem checked24 : verifyInputs db Schreier.initialRelator 1536 indices24 = true := by decide +kernel

private theorem prefix24 (hi : Initial g) : ValidBefore g db 1600 :=
  verifyInputs_sound hi (prefix23 hi) indices24 checked24

def indices25 : List (Fin 14409) := [3906, 3909, 3913, 3916, 3920, 3923, 3927, 3930, 3933, 3934, 3935, 3937, 3940, 3941, 3944, 3962, 3965, 3968, 3975, 3976, 3979, 3983, 3986, 3997, 4000, 4003, 4004, 4005, 4007, 4011, 4018, 4021, 4025, 4028, 4032, 4035, 4038, 4045, 4047, 4054, 4059, 4067, 4070, 4074, 4077, 4081, 4084, 4087, 4088, 4091, 4094, 4095, 4098, 4108, 4109, 4110, 4112, 4116, 4119, 4129, 4130, 4138, 4144, 4147]

private theorem checked25 : verifyInputs db Schreier.initialRelator 1600 indices25 = true := by decide +kernel

private theorem prefix25 (hi : Initial g) : ValidBefore g db 1664 :=
  verifyInputs_sound hi (prefix24 hi) indices25 checked25

def indices26 : List (Fin 14409) := [4151, 4154, 4157, 4172, 4175, 4178, 4179, 4180, 4182, 4186, 4189, 4192, 4194, 4200, 4203, 4206, 4207, 4210, 4214, 4217, 4220, 4221, 4224, 4228, 4231, 4234, 4235, 4238, 4241, 4248, 4249, 4255, 4256, 4259, 4261, 4263, 4266, 4268, 4270, 4273, 4277, 4280, 4284, 4287, 4297, 4298, 4305, 4306, 4308, 4318, 4319, 4322, 4325, 4327, 4333, 4336, 4340, 4353, 4354, 4357, 4359, 4360, 4361, 4364]

private theorem checked26 : verifyInputs db Schreier.initialRelator 1664 indices26 = true := by decide +kernel

private theorem prefix26 (hi : Initial g) : ValidBefore g db 1728 :=
  verifyInputs_sound hi (prefix25 hi) indices26 checked26

def indices27 : List (Fin 14409) := [4367, 4368, 4375, 4378, 4381, 4382, 4385, 4402, 4403, 4404, 4406, 4409, 4410, 4424, 4427, 4431, 4436, 4438, 4444, 4445, 4448, 4452, 4455, 4465, 4466, 4467, 4469, 4472, 4473, 4476, 4480, 4483, 4487, 4490, 4493, 4494, 4497, 4501, 4502, 4508, 4511, 4515, 4518, 4521, 4522, 4525, 4528, 4529, 4532, 4536, 4539, 4542, 4543, 4546, 4550, 4553, 4557, 4560, 4564, 4578, 4581, 4591, 4593, 4598]

private theorem checked27 : verifyInputs db Schreier.initialRelator 1728 indices27 = true := by decide +kernel

private theorem prefix27 (hi : Initial g) : ValidBefore g db 1792 :=
  verifyInputs_sound hi (prefix26 hi) indices27 checked27

def indices28 : List (Fin 14409) := [4606, 4612, 4619, 4620, 4623, 4626, 4627, 4630, 4633, 4634, 4637, 4640, 4641, 4644, 4648, 4651, 4654, 4655, 4658, 4669, 4672, 4682, 4683, 4686, 4689, 4690, 4693, 4697, 4700, 4703, 4704, 4707, 4710, 4711, 4712, 4714, 4718, 4721, 4724, 4733, 4739, 4742, 4745, 4746, 4749, 4753, 4756, 4760, 4763, 4767, 4770, 4782, 4788, 4794, 4796, 4802, 4808, 4809, 4812, 4815, 4823, 4830, 4833, 4836]

private theorem checked28 : verifyInputs db Schreier.initialRelator 1792 indices28 = true := by decide +kernel

private theorem prefix28 (hi : Initial g) : ValidBefore g db 1856 :=
  verifyInputs_sound hi (prefix27 hi) indices28 checked28

def indices29 : List (Fin 14409) := [4845, 4851, 4854, 4857, 4865, 4868, 4872, 4875, 4879, 4882, 4886, 4889, 4899, 4900, 4901, 4903, 4913, 4914, 4917, 4936, 4941, 4955, 4963, 4966, 4969, 4970, 4973, 4977, 4980, 4984, 4987, 5005, 5008, 5012, 5015, 5019, 5022, 5025, 5026, 5029, 5033, 5036, 5040, 5046, 5047, 5050, 5054, 5057, 5060, 5061, 5064, 5068, 5071, 5075, 5078, 5080, 5081, 5082, 5085, 5088, 5089, 5092, 5095, 5103]

private theorem checked29 : verifyInputs db Schreier.initialRelator 1856 indices29 = true := by decide +kernel

private theorem prefix29 (hi : Initial g) : ValidBefore g db 1920 :=
  verifyInputs_sound hi (prefix28 hi) indices29 checked29

def indices30 : List (Fin 14409) := [5106, 5123, 5124, 5127, 5131, 5134, 5138, 5145, 5148, 5151, 5152, 5155, 5158, 5159, 5162, 5166, 5169, 5172, 5179, 5180, 5187, 5190, 5193, 5194, 5197, 5201, 5208, 5211, 5222, 5225, 5229, 5232, 5243, 5246, 5250, 5253, 5257, 5260, 5263, 5264, 5271, 5274, 5277, 5278, 5299, 5302, 5305, 5312, 5313, 5314, 5316, 5320, 5323, 5327, 5328, 5333, 5334, 5337, 5348, 5351, 5362, 5365, 5368, 5369]

private theorem checked30 : verifyInputs db Schreier.initialRelator 1920 indices30 = true := by decide +kernel

private theorem prefix30 (hi : Initial g) : ValidBefore g db 1984 :=
  verifyInputs_sound hi (prefix29 hi) indices30 checked30

def indices31 : List (Fin 14409) := [5372, 5383, 5386, 5390, 5393, 5396, 5397, 5400, 5404, 5417, 5432, 5435, 5446, 5449, 5453, 5456, 5459, 5460, 5463, 5466, 5467, 5470, 5474, 5477, 5479, 5481, 5484, 5488, 5491, 5494, 5495, 5502, 5505, 5508, 5509, 5517, 5522, 5530, 5533, 5536, 5537, 5543, 5544, 5547, 5551, 5554, 5558, 5565, 5568, 5571, 5572, 5573, 5575, 5586, 5589, 5592, 5599, 5600, 5603, 5614, 5617, 5621, 5624, 5627]

private theorem checked31 : verifyInputs db Schreier.initialRelator 1984 indices31 = true := by decide +kernel

private theorem prefix31 (hi : Initial g) : ValidBefore g db 2048 :=
  verifyInputs_sound hi (prefix30 hi) indices31 checked31

def indices32 : List (Fin 14409) := [5628, 5631, 5634, 5641, 5642, 5645, 5662, 5677, 5680, 5690, 5691, 5694, 5697, 5711, 5712, 5715, 5726, 5729, 5733, 5736, 5740, 5741, 5753, 5754, 5760, 5762, 5768, 5771, 5781, 5782, 5788, 5789, 5794, 5795, 5796, 5803, 5806, 5809, 5810, 5813, 5816, 5817, 5820, 5824, 5827, 5837, 5838, 5841, 5845, 5848, 5852, 5855, 5858, 5859, 5862, 5866, 5869, 5880, 5883, 5887, 5890, 5900, 5901, 5904]

private theorem checked32 : verifyInputs db Schreier.initialRelator 2048 indices32 = true := by decide +kernel

private theorem prefix32 (hi : Initial g) : ValidBefore g db 2112 :=
  verifyInputs_sound hi (prefix31 hi) indices32 checked32

def indices33 : List (Fin 14409) := [5907, 5915, 5918, 5922, 5925, 5929, 5932, 5942, 5943, 5946, 5970, 5977, 5978, 5985, 5988, 5998, 5999, 6002, 6005, 6012, 6013, 6016, 6027, 6030, 6033, 6034, 6037, 6040, 6048, 6055, 6058, 6062, 6065, 6069, 6072, 6076, 6082, 6083, 6084, 6086, 6089, 6090, 6093, 6096, 6103, 6104, 6107, 6111, 6114, 6118, 6121, 6124, 6125, 6128, 6131, 6132, 6135, 6138, 6139, 6142, 6145, 6146, 6149, 6152]

private theorem checked33 : verifyInputs db Schreier.initialRelator 2112 indices33 = true := by decide +kernel

private theorem prefix33 (hi : Initial g) : ValidBefore g db 2176 :=
  verifyInputs_sound hi (prefix32 hi) indices33 checked33

def indices34 : List (Fin 14409) := [6153, 6156, 6161, 6166, 6173, 6174, 6177, 6181, 6184, 6187, 6188, 6191, 6201, 6202, 6205, 6216, 6219, 6222, 6230, 6231, 6233, 6237, 6240, 6243, 6244, 6250, 6257, 6258, 6261, 6271, 6278, 6279, 6286, 6289, 6292, 6293, 6296, 6306, 6314, 6328, 6331, 6334, 6342, 6345, 6355, 6356, 6359, 6369, 6383, 6384, 6387, 6391, 6394, 6398, 6399, 6401, 6404, 6405, 6408, 6411, 6412, 6415, 6419, 6422]

private theorem checked34 : verifyInputs db Schreier.initialRelator 2176 indices34 = true := by decide +kernel

private theorem prefix34 (hi : Initial g) : ValidBefore g db 2240 :=
  verifyInputs_sound hi (prefix33 hi) indices34 checked34

def indices35 : List (Fin 14409) := [6425, 6439, 6440, 6443, 6446, 6448, 6460, 6467, 6475, 6478, 6481, 6482, 6485, 6488, 6489, 6503, 6506, 6510, 6513, 6516, 6517, 6520, 6545, 6548, 6551, 6559, 6562, 6567, 6572, 6573, 6576, 6579, 6580, 6583, 6587, 6590, 6593, 6601, 6604, 6607, 6621, 6622, 6625, 6628, 6635, 6636, 6639, 6643, 6650, 6653, 6657, 6660, 6663, 6664, 6667, 6671, 6674, 6677, 6678, 6681, 6684, 6685, 6688, 6691]

private theorem checked35 : verifyInputs db Schreier.initialRelator 2240 indices35 = true := by decide +kernel

private theorem prefix35 (hi : Initial g) : ValidBefore g db 2304 :=
  verifyInputs_sound hi (prefix34 hi) indices35 checked35

def indices36 : List (Fin 14409) := [6692, 6695, 6699, 6702, 6713, 6716, 6720, 6723, 6725, 6726, 6727, 6730, 6733, 6734, 6737, 6744, 6747, 6748, 6751, 6761, 6762, 6765, 6768, 6769, 6772, 6776, 6783, 6786, 6803, 6810, 6811, 6814, 6824, 6832, 6835, 6839, 6845, 6847, 6853, 6856, 6866, 6874, 6877, 6894, 6895, 6898, 6901, 6908, 6915, 6923, 6926, 6929, 6937, 6944, 6947, 6950, 6951, 6964, 6965, 6968, 6971, 6972, 6975, 6978]

private theorem checked36 : verifyInputs db Schreier.initialRelator 2304 indices36 = true := by decide +kernel

private theorem prefix36 (hi : Initial g) : ValidBefore g db 2368 :=
  verifyInputs_sound hi (prefix35 hi) indices36 checked36

def indices37 : List (Fin 14409) := [6986, 7000, 7003, 7021, 7024, 7028, 7035, 7038, 7041, 7042, 7045, 7048, 7063, 7066, 7069, 7083, 7090, 7098, 7112, 7115, 7118, 7119, 7125, 7147, 7150, 7160, 7161, 7164, 7168, 7175, 7178, 7181, 7182, 7185, 7189, 7192, 7195, 7209, 7216, 7217, 7220, 7230, 7259, 7262, 7265, 7266, 7269, 7279, 7286, 7287, 7308, 7311, 7314, 7315, 7318, 7321, 7322, 7325, 7328, 7336, 7339, 7349, 7357, 7360]

private theorem checked37 : verifyInputs db Schreier.initialRelator 2368 indices37 = true := by decide +kernel

private theorem prefix37 (hi : Initial g) : ValidBefore g db 2432 :=
  verifyInputs_sound hi (prefix36 hi) indices37 checked37

def indices38 : List (Fin 14409) := [7364, 7371, 7374, 7385, 7388, 7391, 7399, 7402, 7405, 7427, 7430, 7440, 7454, 7455, 7462, 7468, 7483, 7486, 7497, 7500, 7511, 7514, 7517, 7518, 7521, 7523, 7525, 7528, 7532, 7535, 7538, 7539, 7542, 7545, 7546, 7549, 7553, 7556, 7566, 7567, 7570, 7574, 7577, 7587, 7588, 7591, 7594, 7601, 7602, 7605, 7622, 7636, 7643, 7644, 7658, 7661, 7672, 7675, 7679, 7682, 7685, 7693, 7696, 7707]

private theorem checked38 : verifyInputs db Schreier.initialRelator 2432 indices38 = true := by decide +kernel

private theorem prefix38 (hi : Initial g) : ValidBefore g db 2496 :=
  verifyInputs_sound hi (prefix37 hi) indices38 checked38

def indices39 : List (Fin 14409) := [7710, 7727, 7728, 7731, 7735, 7738, 7742, 7748, 7749, 7752, 7755, 7769, 7790, 7791, 7794, 7812, 7815, 7818, 7840, 7843, 7846, 7853, 7867, 7874, 7875, 7878, 7888, 7903, 7906, 7909, 7916, 7917, 7920, 7923, 7924, 7927, 7930, 7931, 7938, 7941, 7958, 7965, 7972, 7973, 7979, 7980, 7983, 7993, 7994, 7997, 8001, 8004, 8006, 8008, 8011, 8014, 8022, 8025, 8028, 8029, 8032, 8036, 8039, 8043]

private theorem checked39 : verifyInputs db Schreier.initialRelator 2496 indices39 = true := by decide +kernel

private theorem prefix39 (hi : Initial g) : ValidBefore g db 2560 :=
  verifyInputs_sound hi (prefix38 hi) indices39 checked39

def indices40 : List (Fin 14409) := [8046, 8057, 8060, 8063, 8077, 8085, 8088, 8098, 8099, 8112, 8113, 8127, 8130, 8133, 8141, 8144, 8148, 8154, 8161, 8162, 8165, 8169, 8183, 8186, 8190, 8193, 8204, 8207, 8211, 8214, 8217, 8224, 8225, 8228, 8245, 8259, 8266, 8273, 8281, 8284, 8287, 8288, 8291, 8301, 8302, 8305, 8323, 8326, 8329, 8330, 8333, 8337, 8340, 8344, 8347, 8350, 8357, 8358, 8361, 8364, 8372, 8375, 8386, 8393]

private theorem checked40 : verifyInputs db Schreier.initialRelator 2560 indices40 = true := by decide +kernel

private theorem prefix40 (hi : Initial g) : ValidBefore g db 2624 :=
  verifyInputs_sound hi (prefix39 hi) indices40 checked40

def indices41 : List (Fin 14409) := [8396, 8400, 8403, 8407, 8410, 8413, 8414, 8417, 8420, 8421, 8424, 8427, 8428, 8431, 8434, 8438, 8441, 8442, 8463, 8477, 8480, 8483, 8484, 8487, 8491, 8494, 8496, 8497, 8498, 8512, 8515, 8517, 8518, 8526, 8529, 8546, 8547, 8553, 8554, 8569, 8574, 8575, 8578, 8582, 8585, 8589, 8592, 8617, 8620, 8623, 8631, 8634, 8645, 8648, 8651, 8658, 8666, 8669, 8672, 8680, 8683, 8686, 8694, 8701]

private theorem checked41 : verifyInputs db Schreier.initialRelator 2624 indices41 = true := by decide +kernel

private theorem prefix41 (hi : Initial g) : ValidBefore g db 2688 :=
  verifyInputs_sound hi (prefix40 hi) indices41 checked41

def indices42 : List (Fin 14409) := [8704, 8722, 8725, 8728, 8729, 8732, 8756, 8757, 8770, 8778, 8781, 8785, 8788, 8806, 8809, 8812, 8813, 8816, 8819, 8841, 8844, 8869, 8872, 8875, 8889, 8890, 8893, 8917, 8918, 8921, 8924, 8932, 8935, 8946, 8953, 8956, 8966, 8967, 8970, 8973, 8980, 8981, 8984, 8987, 9008, 9009, 9012, 9022, 9023, 9026, 9029, 9030, 9033, 9044, 9047, 9050, 9051, 9054, 9065, 9078, 9086, 9089, 9092, 9099]

private theorem checked42 : verifyInputs db Schreier.initialRelator 2688 indices42 = true := by decide +kernel

private theorem prefix42 (hi : Initial g) : ValidBefore g db 2752 :=
  verifyInputs_sound hi (prefix41 hi) indices42 checked42

def indices43 : List (Fin 14409) := [9107, 9110, 9121, 9124, 9127, 9134, 9141, 9148, 9156, 9159, 9163, 9166, 9170, 9173, 9184, 9187, 9205, 9208, 9211, 9212, 9215, 9218, 9219, 9222, 9225, 9247, 9250, 9254, 9257, 9260, 9268, 9271, 9281, 9289, 9338, 9352, 9355, 9358, 9359, 9362, 9400, 9415, 9418, 9429, 9432, 9435, 9457, 9460, 9463, 9464, 9467, 9470, 9478, 9481, 9491, 9512, 9526, 9527, 9530, 9533, 9548, 9551, 9582, 9583]

private theorem checked43 : verifyInputs db Schreier.initialRelator 2752 indices43 = true := by decide +kernel

private theorem prefix43 (hi : Initial g) : ValidBefore g db 2816 :=
  verifyInputs_sound hi (prefix42 hi) indices43 checked43

def indices44 : List (Fin 14409) := [9586, 9589, 9590, 9593, 9596, 9603, 9611, 9614, 9618, 9621, 9625, 9628, 9632, 9635, 9639, 9642, 9660, 9663, 9667, 9673, 9687, 9695, 9698, 9701, 9702, 9705, 9708, 9722, 9736, 9744, 9747, 9764, 9779, 9782, 9792, 9799, 9820, 9827, 9828, 9831, 9848, 9855, 9869, 9870, 9873, 9876, 9883, 9884, 9887, 9890, 9912, 9915, 9918, 9926, 9929, 9939, 9940, 9943, 9945, 9946, 9947, 9950, 9953, 9961]

private theorem checked44 : verifyInputs db Schreier.initialRelator 2816 indices44 = true := by decide +kernel

private theorem prefix44 (hi : Initial g) : ValidBefore g db 2880 :=
  verifyInputs_sound hi (prefix43 hi) indices44 checked44

def indices45 : List (Fin 14409) := [9964, 9967, 9968, 9974, 9975, 9978, 9988, 10010, 10013, 10024, 10027, 10037, 10038, 10041, 10058, 10087, 10090, 10101, 10104, 10121, 10135, 10136, 10139, 10142, 10157, 10160, 10163, 10191, 10206, 10209, 10220, 10223, 10248, 10251, 10269, 10272, 10274, 10276, 10279, 10282, 10283, 10286, 10290, 10293, 10303, 10304, 10307, 10310, 10325, 10338, 10346, 10349, 10353, 10356, 10360, 10363, 10365, 10367, 10370, 10374, 10380, 10387, 10388, 10391]

private theorem checked45 : verifyInputs db Schreier.initialRelator 2880 indices45 = true := by decide +kernel

private theorem prefix45 (hi : Initial g) : ValidBefore g db 2944 :=
  verifyInputs_sound hi (prefix44 hi) indices45 checked45

def indices46 : List (Fin 14409) := [10395, 10398, 10402, 10405, 10408, 10415, 10422, 10430, 10433, 10436, 10451, 10454, 10457, 10458, 10461, 10471, 10472, 10475, 10478, 10486, 10489, 10499, 10506, 10520, 10521, 10524, 10527, 10528, 10531, 10541, 10548, 10562, 10563, 10566, 10569, 10584, 10587, 10590, 10591, 10594, 10598, 10601, 10605, 10608, 10625, 10640, 10643, 10646, 10653, 10668, 10671, 10682, 10685, 10696, 10699, 10703, 10706, 10709, 10723, 10730, 10737, 10758, 10766, 10769]

private theorem checked46 : verifyInputs db Schreier.initialRelator 2944 indices46 = true := by decide +kernel

private theorem prefix46 (hi : Initial g) : ValidBefore g db 3008 :=
  verifyInputs_sound hi (prefix45 hi) indices46 checked46

def indices47 : List (Fin 14409) := [10772, 10780, 10783, 10786, 10800, 10807, 10821, 10822, 10825, 10835, 10836, 10839, 10842, 10849, 10856, 10857, 10885, 10888, 10898, 10905, 10913, 10916, 10920, 10923, 10933, 10934, 10937, 10940, 10948, 10951, 10962, 10965, 10975, 10989, 10996, 11003, 11010, 11039, 11042, 11052, 11059, 11066, 11073, 11080, 11081, 11088, 11091, 11094, 11109, 11112, 11129, 11130, 11133, 11143, 11171, 11185, 11200, 11203, 11206, 11213, 11220, 11227, 11228, 11231]

private theorem checked47 : verifyInputs db Schreier.initialRelator 3008 indices47 = true := by decide +kernel

private theorem prefix47 (hi : Initial g) : ValidBefore g db 3072 :=
  verifyInputs_sound hi (prefix46 hi) indices47 checked47

def indices48 : List (Fin 14409) := [11234, 11235, 11238, 11241, 11248, 11262, 11276, 11283, 11284, 11287, 11318, 11332, 11333, 11336, 11347, 11350, 11353, 11368, 11371, 11374, 11396, 11399, 11430, 11437, 11452, 11455, 11458, 11459, 11462, 11466, 11469, 11493, 11508, 11511, 11528, 11536, 11539, 11549, 11563, 11577, 11578, 11581, 11605, 11626, 11633, 11634, 11637, 11640, 11648, 11651, 11655, 11658, 11662, 11665, 11675, 11690, 11693, 11696, 11697, 11700, 11731, 11739, 11742, 11745]

private theorem checked48 : verifyInputs db Schreier.initialRelator 3072 indices48 = true := by decide +kernel

private theorem prefix48 (hi : Initial g) : ValidBefore g db 3136 :=
  verifyInputs_sound hi (prefix47 hi) indices48 checked48

def indices49 : List (Fin 14409) := [11746, 11749, 11759, 11766, 11822, 11823, 11826, 11829, 11830, 11833, 11837, 11840, 11851, 11854, 11857, 11864, 11879, 11882, 11885, 11899, 11907, 11910, 11913, 11921, 11924, 11927, 11934, 11970, 11973, 11976, 11983, 11998, 12001, 12005, 12008, 12025, 12032, 12046, 12053, 12067, 12074, 12081, 12088, 12102, 12109, 12123, 12158, 12159, 12162, 12165, 12193, 12214, 12221, 12235, 12264, 12267, 12277, 12278, 12291, 12298, 12312, 12326, 12333, 12354]

private theorem checked49 : verifyInputs db Schreier.initialRelator 3136 indices49 = true := by decide +kernel

private theorem prefix49 (hi : Initial g) : ValidBefore g db 3200 :=
  verifyInputs_sound hi (prefix48 hi) indices49 checked49

def indices50 : List (Fin 14409) := [12410, 12417, 12431, 12432, 12435, 12445, 12453, 12456, 12494, 12495, 12498, 12502, 12505, 12516, 12519, 12543, 12557, 12579, 12582, 12592, 12593, 12596, 12599, 12600, 12628, 12631, 12634, 12641, 12662, 12669, 12676, 12690, 12698, 12701, 12704, 12711, 12718, 12725, 12732, 12746, 12747, 12753, 12782, 12785, 12788, 12795, 12837, 12838, 12841, 12851, 12872, 12873, 12876, 12879, 12880, 12883, 12893, 12900, 12914, 12928, 12935, 12949, 12964, 12967]

private theorem checked50 : verifyInputs db Schreier.initialRelator 3200 indices50 = true := by decide +kernel

private theorem prefix50 (hi : Initial g) : ValidBefore g db 3264 :=
  verifyInputs_sound hi (prefix49 hi) indices50 checked50

def indices51 : List (Fin 14409) := [12985, 12988, 13020, 13023, 13040, 13041, 13044, 13047, 13054, 13055, 13058, 13061, 13089, 13090, 13093, 13096, 13110, 13124, 13145, 13153, 13156, 13159, 13187, 13201, 13208, 13215, 13230, 13233, 13236, 13243, 13251, 13254, 13264, 13265, 13268, 13271, 13286, 13289, 13313, 13334, 13355, 13362, 13376, 13391, 13394, 13397, 13404, 13419, 13422, 13432, 13446, 13460, 13467, 13474, 13488, 13489, 13492, 13495, 13502, 13509, 13510, 13516, 13524, 13527]

private theorem checked51 : verifyInputs db Schreier.initialRelator 3264 indices51 = true := by decide +kernel

private theorem prefix51 (hi : Initial g) : ValidBefore g db 3328 :=
  verifyInputs_sound hi (prefix50 hi) indices51 checked51

def indices52 : List (Fin 14409) := [13530, 13538, 13565, 13572, 13573, 13600, 13622, 13628, 13656, 13674, 13685, 13688, 13698, 13712, 13726, 13747, 13762, 13765, 13768, 13775, 13803, 13810, 13817, 13825, 13828, 13859, 13873, 13880, 13901, 13922, 13929, 13950, 13964, 13992, 14041, 14069, 14090, 14097, 14125, 14126, 14129, 14146, 14153, 14167, 14175, 14178, 14195, 14202, 14209, 14216, 14237, 14251, 14252, 14258, 14272, 14273, 14293, 14300, 14328, 14335, 14342, 14363, 14384, 14391]

private theorem checked52 : verifyInputs db Schreier.initialRelator 3328 indices52 = true := by decide +kernel

private theorem prefix52 (hi : Initial g) : ValidBefore g db 3392 :=
  verifyInputs_sound hi (prefix51 hi) indices52 checked52

def indices53 : List (Fin 14409) := [14406, 14407, 14408]

private theorem checked53 : verifyInputs db Schreier.initialRelator 3392 indices53 = true := by decide +kernel

private theorem prefix53 (hi : Initial g) : ValidBefore g db 3395 :=
  verifyInputs_sound hi (prefix52 hi) indices53 checked53

theorem valid (hi : Initial g) : ValidBefore g db initialCount := prefix53 hi

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Initials
