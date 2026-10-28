module
public import Theory.Representation.Mathieu.M22James.SolvableOvergroup.Generators
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
/-!
# A solvable overgroup escaping the triple-Mathieu scalar plane

Eight certified two-elements give 256 distinct elements in a common binary
triangular subgroup. The known order of the full covering extension bounds
its two-part by 256, so this is an actual Sylow subgroup. Nine checked right
cosets cover the subgroup generated with the central cubic and a moving
involution. Its order is 256·9; the proved two-prime theorem gives solvability.

A binary coordinate inverse certifies distinctness. The existing proved XOR
row checker certifies matrix products, without large repeated reductions.
The chosen Sylow fixes the last coordinate vector, and the moving involution
sends that vector outside its scalar plane. Conjugacy and normality of the
scalar cubic transfer the construction to every original Sylow marking.

Source: Aschbacher–Smith 14.7.36, printed p.1059, and H.12.1, printed pp.393–394.
The native ATLAS attribution is retained by `SolvableOvergroup.Generators`.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open scoped Matrix
namespace Sporadic.Mathieu.M22TripleCover.Escape
open Ambient Certificate
private def parentBlocks : Fin 16 → Fin 16 → Fin 256 := ![
![0,0,0,1,0,1,2,3,0,1,2,3,4,5,6,7],
![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
![16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],
![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
![16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],
![32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47],
![48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],
![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
![16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],
![32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47],
![48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],
![64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79],
![80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95],
![96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111],
![112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127]]
private def parent (n : Fin 256) : Fin 256 := parentBlocks ⟨n.val / 16,by omega⟩ ⟨n.val % 16,by omega⟩
private def lastBlocks : Fin 16 → Fin 16 → Fin 8 := ![
![0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3],
![4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4],
![5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
![5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
![6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
![6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
![6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
![6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
![7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7]]
private def last (n : Fin 256) : Fin 8 := lastBlocks ⟨n.val / 16,by omega⟩ ⟨n.val % 16,by omega⟩
private theorem parent_lt : ∀ n : Fin 256, n ≠ 0 → (parent n).val < n.val := by decide +kernel
private def elements (n : Fin 256) : actionGroup :=
  if _hn : n = 0 then 1 else elements (parent n) * pc (last n)
termination_by n.val
decreasing_by exact parent_lt n _hn
private def tableBlocks : Fin 16 → Fin 16 → Array ℕ := ![
![#[ 1,2,4,8,16,32,64,128,256,512,1024,2048],#[ 916,1735,1129,558,472,174,1648,14,1432,38,1888,3819],#[ 551,1543,312,1303,2017,1773,116,1451,1055,1012,1774,2837],#[ 1177,1501,1863,1841,822,366,1122,552,1452,466,1948,3082],#[ 916,1735,1130,556,1265,175,858,922,1505,1761,1818,3781],#[ 1,2,1367,1743,1020,948,1791,129,1980,514,2031,2094],#[ 1911,194,915,1843,2017,1094,878,1713,254,1012,277,3786],#[ 457,792,1657,976,1523,1685,552,1122,1928,1815,1335,3380],#[ 509,867,504,673,2018,1582,444,380,937,1703,147,4082],#[ 616,1426,1117,179,1578,1896,1604,58,1797,1205,527,3863],#[ 1007,1362,196,1982,654,638,392,1111,1718,1530,224,3355],#[ 1361,1724,1863,1452,1625,1025,1122,552,1841,2024,90,3747],#[ 616,1426,1731,976,98,1685,658,594,1065,295,957,2307],#[ 509,867,1538,1843,1883,1094,1791,129,1652,1476,692,2534],#[ 1675,931,270,1743,654,948,678,1913,310,1530,1102,2244],#[ 53,77,1304,556,168,175,552,1122,1600,281,400,3324]],
![#[ 1848,855,1128,1841,1330,366,1869,1933,1549,1143,278,3703],#[ 1197,1446,1852,1303,1230,1773,1648,14,661,1617,1359,2534],#[ 1310,1382,1376,558,1530,174,1913,678,786,654,1217,2671],#[ 928,1672,1062,8,281,32,1122,552,673,168,650,2823],#[ 1197,1446,851,1600,690,469,1123,1187,397,1015,568,2182],#[ 1848,855,1379,663,1471,1475,1739,181,996,1824,1524,3863],#[ 122,919,1194,863,1530,356,1111,392,1170,654,111,4016],#[ 1732,121,1657,1928,2024,1166,552,1122,976,1625,832,2392],#[ 1776,54,1440,1452,405,1025,1669,1605,1168,901,1744,2768],#[ 1381,1779,1800,1982,105,638,1604,58,60,407,833,2094],#[ 1250,1587,1192,179,1012,1896,1713,878,399,2017,430,3840],#[ 604,1513,1062,673,1815,1582,1122,552,8,1523,1561,2458],#[ 1381,1779,462,1928,1396,1166,1439,1375,113,1892,1482,3093],#[ 1776,54,1590,863,589,356,1739,181,536,947,974,3819],#[ 434,246,1539,663,1012,1475,1451,116,1390,2017,1621,2783],#[ 1804,812,1304,1600,466,469,552,1122,556,822,1202,2212]],
![#[ 1776,1309,1519,1549,1265,298,64,128,538,1761,1019,3589],#[ 1381,984,620,308,38,1877,129,1791,925,472,1642,3861],#[ 457,792,460,786,26,482,116,1451,1797,1039,527,3344],#[ 1911,194,322,1067,466,1423,1932,454,937,822,147,3822],#[ 1381,984,385,1065,16,421,858,922,1787,512,225,2240],#[ 1776,1309,850,1493,514,1103,14,1648,441,1020,1765,2512],#[ 1177,1501,871,310,26,841,878,1713,996,1039,1524,2255],#[ 551,1543,124,202,1815,628,454,1932,397,1523,568,4048],#[ 531,1660,268,443,1015,719,1187,1123,1452,690,1948,2307],#[ 390,141,600,1718,1824,103,181,1739,1055,1471,1774,3062],#[ 1310,77,1327,1188,158,1413,1175,328,179,2026,490,3829],#[ 928,931,322,937,342,1291,1932,454,1067,231,1953,2392],#[ 390,141,1591,202,1143,628,1933,1869,556,1330,1202,4082],#[ 531,1660,7,310,1617,841,14,1648,1390,1230,1621,3335],#[ 122,1724,1253,1493,158,1103,1977,614,1843,2026,1348,2858],#[ 1732,1362,797,1065,1959,421,454,1932,1370,1558,1643,2823]],
![#[ 1238,1608,1180,1067,295,1423,594,658,8,98,1561,2182],#[ 1859,185,313,786,1476,482,129,1791,399,1883,430,3335],#[ 1007,121,139,308,2026,1877,614,1977,1303,158,1483,2433],#[ 1361,919,547,1549,1558,298,1932,454,443,1959,1393,3324],#[ 1859,185,935,1370,1703,1332,380,444,1928,2018,1335,3703],#[ 1238,1608,870,1170,1205,716,58,1604,254,1578,277,3062],#[ 1675,1672,321,69,2026,1695,328,1175,663,158,357,3166],#[ 53,1382,124,397,231,1412,454,1932,202,342,1211,3747],#[ 1,1321,75,937,1396,1291,1669,1605,1930,1892,299,3285],#[ 916,1004,269,1188,407,1413,181,1739,1593,105,587,2512],#[ 1804,812,1116,1718,1039,103,1713,878,661,26,1359,2309],#[ 434,246,547,443,1523,719,1932,454,1549,1815,278,2942],#[ 916,1004,1061,397,405,1412,1439,1375,875,901,561,2576],#[ 1,1321,51,69,947,1695,58,1604,1053,589,708,3861],#[ 604,1513,1783,1170,1039,716,1451,116,1652,26,692,3290],#[ 1250,1587,797,1370,822,1332,454,1932,1065,466,957,2624]],
![#[ 509,1513,4,256,148,164,64,128,8,624,147,3095],#[ 616,1587,138,1593,348,1225,659,1261,399,1353,527,2948],#[ 1732,1779,312,1055,882,638,116,1451,1303,652,1642,3842],#[ 122,54,1723,806,1957,1025,1438,980,443,1461,1019,2157],#[ 616,1587,1182,976,414,1332,1605,1669,258,890,1686,4045],#[ 509,1513,1119,1843,908,716,1795,381,863,1945,1951,2142],#[ 1675,1321,1656,1743,882,1342,1649,942,1053,652,357,2781],#[ 53,1004,622,556,1151,782,980,1438,875,1647,1211,3256],#[ 1,1672,504,937,1894,1706,444,380,673,1751,1024,3045],#[ 916,1382,190,1188,1710,783,679,1241,786,474,1888,2680],#[ 1804,1446,196,1718,1565,1773,392,1111,1982,1154,100,2316],#[ 434,855,1723,443,714,366,1438,980,806,911,1085,2756],#[ 916,1382,1591,556,1293,782,1933,1869,202,1212,561,2059],#[ 1,1672,1802,1743,1835,1342,1795,381,663,95,708,2454],#[ 1911,1608,1253,1843,1565,716,1977,614,1493,1154,1086,3283],#[ 457,185,271,976,292,1332,980,1438,675,97,28,3440]],
![#[ 987,1724,375,806,1346,1025,594,658,538,1267,1393,2708],#[ 78,1362,991,1055,1214,638,659,1261,925,970,1483,2454],#[ 1250,1426,127,1593,1154,1225,614,1977,1797,1565,430,2963],#[ 604,867,1498,256,97,164,1438,980,937,292,1561,2687],#[ 78,1362,1720,675,1833,421,1123,1187,113,1688,832,2426],#[ 987,1724,1131,1652,1339,1103,1847,329,536,591,111,2680],#[ 1177,1660,1118,1980,1154,232,1111,392,1390,1565,1524,3660],#[ 551,141,622,875,911,1278,980,1438,556,714,568,3531],#[ 531,1501,191,443,485,366,922,858,135,769,695,3635],#[ 390,1543,1003,1718,25,1773,679,1241,308,1036,965,2142],#[ 1310,1735,439,1188,652,783,942,1649,1432,882,1217,3836],#[ 928,2,1498,937,1647,1706,1438,980,256,1151,650,2274],#[ 390,1543,1061,875,239,1278,1439,1375,397,523,1202,3561],#[ 531,1501,1854,1980,713,232,1847,329,996,1756,1621,2948],#[ 1361,1309,1783,1652,652,1103,1451,116,1170,882,974,2851],#[ 1007,984,271,675,1461,421,980,1438,976,1957,1482,3127]],
![#[ 531,246,1519,538,414,1093,64,128,1549,890,1948,3853],#[ 390,812,912,60,1353,966,381,1795,661,348,1774,3985],#[ 53,1004,460,1797,1149,1413,116,1451,786,1411,1888,3096],#[ 1675,1321,1441,1315,1461,1291,879,1317,673,1957,1024,2685],#[ 390,812,373,202,148,469,1605,1669,1799,624,409,3287],#[ 531,246,1861,310,1945,1475,1261,659,69,908,894,3147],#[ 122,54,1676,1493,1149,709,1649,942,536,1411,111,2503],#[ 1732,1779,372,1065,1647,516,1317,879,113,1151,832,3752],#[ 1776,919,268,1452,1688,1952,1187,1123,443,1833,1019,2059],#[ 1381,121,932,1982,591,1268,329,1847,1303,1339,1642,2930],#[ 1250,185,1327,179,1273,482,1175,328,1188,1638,1157,4093],#[ 604,1608,1441,673,1329,1423,879,1317,1315,1140,818,3531],#[ 1381,121,1731,1065,1267,516,658,594,976,1346,1482,3045],#[ 1776,919,1040,1493,970,709,1261,659,1170,1214,974,2204],#[ 1177,855,270,310,1273,1475,678,1913,1743,1638,223,2594],#[ 551,1446,533,202,1759,469,1317,879,1190,1946,1811,2687]],
![#[ 1322,931,387,1315,1212,1291,1869,1933,256,1293,650,2426],#[ 1727,77,197,1797,95,1413,381,1795,1432,1835,1217,2204],#[ 1804,141,1428,60,1638,966,1913,678,1055,1273,1359,3426],#[ 434,1660,1728,538,1946,1093,879,1317,1452,1759,278,3440],#[ 1727,77,1612,1190,1751,175,380,444,875,1894,1211,2708],#[ 1322,931,1905,1390,474,948,1241,679,1053,1710,357,2930],#[ 1911,867,437,441,1638,2023,328,1175,1652,1273,277,2237],#[ 457,1426,372,113,1140,31,1317,879,1065,1329,1335,2756],#[ 509,194,1364,673,239,1423,922,858,1666,523,1464,3369],#[ 616,792,241,179,1036,482,329,1847,558,25,1828,3147],#[ 1007,984,323,1982,1411,1268,942,1649,925,1149,1483,3558],#[ 1361,1309,1728,1452,1151,1952,879,1317,538,1647,1393,2802],#[ 616,792,462,113,485,31,1439,1375,1928,769,957,3827],#[ 509,194,1060,441,1756,2023,1241,679,254,713,692,3985],#[ 928,2,1539,1390,1411,948,1451,116,663,1149,708,2105],#[ 1310,1735,533,1190,1957,175,1317,879,202,1461,561,3623]],
![#[ 1322,2,1307,1315,901,1706,1375,1439,1067,405,1953,2240],#[ 1727,1735,1117,1797,589,783,1604,58,179,947,490,2197],#[ 1804,1543,1063,60,351,1356,1387,180,308,1354,100,3786],#[ 434,1501,1907,538,1416,2020,1110,540,135,1900,1085,2624],#[ 1727,1735,373,1799,1892,1573,1605,1669,202,1396,1211,3589],#[ 1322,2,1379,996,105,21,1739,181,663,407,357,3664],#[ 604,194,1676,536,351,2023,1649,942,1493,1354,1951,2837],#[ 1250,792,1613,1787,845,31,540,1110,675,425,1686,2942],#[ 1238,867,1255,1930,1143,164,1187,1123,1666,1330,818,3890],#[ 1859,1426,1129,1432,1471,1225,1648,14,558,1824,1157,2409],#[ 1732,1362,1499,661,1072,479,1175,328,925,836,1642,2244],#[ 122,1724,1907,135,231,651,1110,540,538,342,1019,2281],#[ 1859,1426,988,1787,1015,31,1933,1869,258,690,28,2499],#[ 1238,867,1590,536,1230,2023,1739,181,863,1617,1086,3992],#[ 928,931,1041,996,1072,21,1977,614,1053,836,708,3355],#[ 1310,77,1324,1799,1558,1573,540,1110,875,1959,561,2742]],
![#[ 531,855,375,538,1703,2020,594,658,806,2018,695,3767],#[ 390,1446,1800,60,1883,1356,1604,58,1982,1476,965,3992],#[ 53,1382,127,1797,836,783,614,1977,1593,1072,587,4016],#[ 1675,1672,1042,1315,1959,1706,1110,540,1930,1558,299,3405],#[ 390,1446,1612,875,295,1887,380,444,1190,98,409,2118],#[ 531,855,1367,1980,1578,1634,1791,129,1743,1205,894,2409],#[ 1361,919,437,1652,836,709,328,1175,441,1072,1765,2671],#[ 1007,121,1613,675,342,516,540,1110,1787,231,225,3858],#[ 987,54,191,135,512,651,922,858,443,16,1393,2576],#[ 78,1779,1852,661,1020,479,1648,14,1303,514,1483,3664],#[ 457,1587,439,1432,1354,1225,942,1649,1188,351,1828,2783],#[ 1911,1513,1042,1930,425,164,1110,540,1315,845,1464,4048],#[ 78,1779,1233,675,1761,516,128,64,1370,1265,1643,3285],#[ 987,54,1538,1652,472,709,1791,129,1843,38,1348,2197],#[ 1177,246,796,1980,1354,1634,180,1387,69,351,223,3840],#[ 551,812,1324,875,1900,1887,540,1110,1799,1416,1811,3822]],
![#[ 987,1309,240,806,1892,1952,1375,1439,1841,1396,90,3781],#[ 78,984,600,1055,947,1268,181,1739,1718,589,224,2411],#[ 1250,792,1235,1593,1700,579,1387,180,558,689,1157,2255],#[ 604,194,374,256,1900,773,1976,498,1666,1416,818,2212],#[ 78,984,1182,258,901,1839,1605,1669,976,405,832,2048],#[ 987,1309,870,254,407,2030,58,1604,1170,105,111,4014],#[ 434,1501,1656,1053,1700,232,1649,942,1743,689,894,3344],#[ 1804,1543,72,1505,425,1278,498,1976,1190,845,409,2458],#[ 1848,1660,1043,1168,98,1093,444,380,135,295,1085,2499],#[ 1197,141,620,925,1205,966,129,1791,308,1578,100,3464],#[ 53,77,48,399,1568,1572,392,1111,1432,340,1888,2858],#[ 1675,931,374,1666,2024,897,1976,498,256,1625,1024,3858],#[ 1197,141,808,1505,2018,1278,658,594,1799,1703,1811,3890],#[ 1848,1660,51,1053,1476,232,58,1604,69,1883,223,2937],#[ 1361,1724,506,254,1568,2030,678,1913,536,340,974,3829],#[ 1007,1362,809,258,281,1839,498,1976,113,168,1482,3405]],
![#[ 509,1608,387,256,690,773,1869,1933,1315,1015,1464,2118],#[ 616,185,269,1593,1617,579,181,1739,1188,1230,1828,2937],#[ 1732,121,1428,1055,340,1268,1913,678,60,1568,833,3166],#[ 122,919,535,806,168,1952,1976,498,1168,281,1744,2742],#[ 616,185,1720,113,1330,958,1123,1187,675,1143,1686,3767],#[ 509,1608,850,441,1824,365,14,1648,1493,1471,1951,3464],#[ 928,1672,1118,1390,340,1342,1111,392,1980,1568,2031,2433],#[ 1310,1382,72,1190,1625,782,498,1976,1505,2024,1818,2281],#[ 1322,1321,1364,1666,1761,897,922,858,673,1265,650,3093],#[ 1727,1004,313,399,514,1572,129,1791,786,1020,1217,4014],#[ 551,812,323,925,689,966,942,1649,1982,1700,965,3290],#[ 1177,246,535,1168,845,1093,1976,498,806,425,695,3380],#[ 1727,1004,314,1190,512,782,128,64,1600,16,400,2768],#[ 1322,1321,7,1390,38,1342,14,1648,310,472,1102,2411],#[ 1911,1513,1000,441,689,365,180,1387,863,1700,1086,2309],#[ 457,1587,809,113,1416,958,498,1976,258,1900,28,3082]],
![#[ 1238,1513,1307,1067,769,1582,1375,1439,1315,485,818,3287],#[ 1859,1587,190,786,713,1896,679,1241,1188,1756,1157,3578],#[ 1007,1779,1063,308,1484,479,1387,180,60,1074,224,2781],#[ 1361,54,1679,1549,283,651,1450,992,1168,779,90,3623],#[ 1859,1587,385,1787,523,958,858,922,1065,239,1335,3853],#[ 1238,1513,1131,536,25,365,1847,329,1652,1036,277,3616],#[ 928,1321,871,996,1484,1695,878,1713,310,1074,2031,3842],#[ 1310,1004,602,1799,705,1412,992,1450,1600,209,1818,2802],#[ 1322,1672,1255,1666,1267,32,1187,1123,1930,1346,1953,2853],#[ 1727,1382,138,399,1339,174,659,1261,1593,591,490,3078],#[ 551,1446,1499,925,163,1356,1175,328,661,572,1774,3283],#[ 1177,855,1679,1168,1140,2020,1450,992,1549,1329,1948,3214],#[ 1727,1382,808,1799,1688,1412,658,594,1505,1833,400,2251],#[ 1322,1672,1854,996,1214,1695,1847,329,1980,970,1102,4072],#[ 604,1608,506,536,163,365,678,1913,254,572,692,2316],#[ 1250,185,315,1787,1946,958,992,1450,1928,1759,957,2874]],
![#[ 1776,1724,1128,1549,1751,651,1869,1933,1841,1894,1744,2644],#[ 1381,1362,1003,308,1835,479,679,1241,1718,95,833,4072],#[ 457,1426,1376,786,572,1896,1913,678,558,163,1828,3660],#[ 1911,867,1518,1067,1759,1582,1450,992,1666,1946,1464,3125],#[ 1381,1362,935,1928,1212,1839,380,444,1370,1293,225,2490],#[ 1776,1724,1119,863,1710,2030,1795,381,1843,474,1765,3078],#[ 434,1660,321,663,572,841,328,1175,69,163,894,2963],#[ 1804,141,602,1600,1329,628,992,1450,1799,1140,409,2945],#[ 1848,1501,1440,1168,624,2020,1669,1605,1452,148,278,3827],#[ 1197,1543,991,925,908,1356,659,1261,1055,1945,1359,3616],#[ 53,1735,1192,399,1074,174,1713,878,179,1484,587,2851],#[ 1675,2,1518,1666,209,32,1450,992,1067,705,299,3752],#[ 1197,1543,314,1600,890,628,128,64,1190,414,1811,3369],#[ 1848,1501,1802,663,348,841,1795,381,1743,1353,223,3578],#[ 122,1309,1000,863,1074,2030,180,1387,441,1484,1348,3836],#[ 1732,984,315,1928,779,1839,992,1450,1787,283,1643,2685]],
![#[ 1848,246,240,1841,523,719,1375,1439,806,239,1085,4045],#[ 1197,812,932,1303,1756,103,329,1847,1982,713,100,2543],#[ 1310,1004,1235,558,707,1572,1387,180,1593,829,490,2503],#[ 928,1321,1429,8,779,897,859,1297,1930,283,1953,3127],#[ 1197,812,1130,1505,769,1887,858,922,556,485,568,3095],#[ 1848,246,1905,1053,1036,1634,1241,679,1390,25,1524,2613],#[ 1361,54,915,254,707,356,878,1713,1843,829,1765,3096],#[ 1007,1779,320,258,209,1166,1297,859,1370,705,225,2274],#[ 987,919,1043,135,1293,298,444,380,1168,1212,90,2251],#[ 78,121,912,661,474,1877,381,1795,60,1710,224,3340],#[ 457,185,48,1432,583,579,392,1111,399,216,527,2594],#[ 1911,1608,1429,1930,911,773,859,1297,8,714,147,2945],#[ 78,121,988,258,1894,1166,1933,1869,1787,1751,1643,2853],#[ 987,919,1060,254,95,356,1241,679,441,1835,1348,3810],#[ 434,855,1041,1053,583,1634,1977,614,996,216,1621,4093],#[ 1804,1446,545,1505,97,1887,1297,859,397,292,1202,3125]],
![#[ 1,931,1180,8,1833,897,594,658,1067,1688,299,2490],#[ 916,77,241,558,970,1572,329,1847,179,1214,587,3810],#[ 551,141,139,1303,216,103,614,1977,308,583,965,2237],#[ 1177,1660,1780,1841,292,719,859,1297,135,97,695,2874],#[ 916,77,851,397,1346,1573,1123,1187,1600,1267,1818,2644],#[ 1,931,1861,69,591,21,1261,659,310,1339,2031,3340],#[ 604,867,1194,1170,216,1094,1111,392,863,583,1951,3426],#[ 1250,1426,320,1370,714,1685,1297,859,258,911,1686,3214],#[ 1238,194,75,1930,890,773,1669,1605,937,414,1561,3561],#[ 1859,792,197,1432,1945,579,381,1795,1797,908,430,2613],#[ 1732,984,1116,661,829,1877,1713,878,1718,707,833,2105],#[ 122,1309,1780,135,705,298,859,1297,1841,209,1744,3256],#[ 1859,792,1233,1370,624,1685,128,64,675,148,28,3635],#[ 1238,194,1040,1170,1353,1094,1261,659,1493,348,1086,2543],#[ 1675,2,796,69,829,21,180,1387,1980,707,1102,3558],#[ 53,1735,545,397,283,1573,1297,859,1505,779,400,2157]]]
private def tableRows (n : Fin 256) : Array ℕ := tableBlocks ⟨n.val / 16,by omega⟩ ⟨n.val % 16,by omega⟩
private def table (n : Fin 256) : Matrix12 := Thompson.BinaryMatrix.decode 12 (tableRows n)
private theorem table_zero : table 0 = 1 := by decide +kernel
private def pcRows : Fin 8 → Array ℕ := ![#[916,1735,1129,558,472,174,1648,14,1432,38,1888,3819],#[551,1543,312,1303,2017,1773,116,1451,1055,1012,1774,2837],#[916,1735,1130,556,1265,175,858,922,1505,1761,1818,3781],#[509,867,504,673,2018,1582,444,380,937,1703,147,4082],#[1848,855,1128,1841,1330,366,1869,1933,1549,1143,278,3703],#[1776,1309,1519,1549,1265,298,64,128,538,1761,1019,3589],#[509,1513,4,256,148,164,64,128,8,624,147,3095],#[1322,2,1307,1315,901,1706,1375,1439,1067,405,1953,2240]]
private theorem pc_decode (i : Fin 8) : pcMatrices i = Thompson.BinaryMatrix.decode 12 (pcRows i) := by
  revert i
  decide +kernel
private theorem table_step (n : Fin 256) (hn : n ≠ 0) :
    table (parent n) * pcMatrices (last n) = table n := by
  rw [pc_decode]
  apply Thompson.BinaryMatrix.decode_mul
  have h : ∀ n : Fin 256, n ≠ 0 → ∀ i : Fin 12,
      Thompson.BinaryMatrix.rowProduct (tableRows (parent n))[i.val]! (pcRows (last n)) 12 =
        (tableRows n)[i.val]! := by decide +kernel
  exact h n hn

private theorem elements_matrix (n : Fin 256) : ((elements n : Matrix12ˣ) : Matrix12) = table n := by
  induction n using elements.induct with
  | case1 =>
    rw [elements,dif_pos rfl]
    exact table_zero.symm
  | case2 n hn ih =>
    rw [elements, dif_neg hn]
    change ((elements (parent n) : Matrix12ˣ) : Matrix12) * ((pc (last n) : Matrix12ˣ) : Matrix12) = _
    rw [ih,pc_matrix,table_step n hn]
private theorem elements_mem (n : Fin 256) : elements n ∈ H ∧ elements n ∈ lower := by
  induction n using elements.induct with
  | case1 =>
    rw [elements,dif_pos rfl]
    exact ⟨H.one_mem,lower.one_mem⟩
  | case2 n hn ih =>
    rw [elements,dif_neg hn]
    exact ⟨H.mul_mem ih.1 (pc_mem _),lower.mul_mem ih.2 (pc_lower _)⟩
private def fingerprint (M : Matrix12) : ℕ :=
  ((List.finRange 11).map (fun i => if M (![0,0,0,0,0,1,1,2,11,2,3] i) (![0,1,2,3,4,0,1,0,7,1,7] i) = 1 then 2^i.val else 0)).sum
private def inverseCodes : Array ℕ := #[0,0,0,0,0,33,0,0,0,34,0,0,0,0,161,0,208,0,115,0,0,98,0,0,0,243,0,0,0,0,0,0,0,0,0,0,178,0,0,0,0,0,0,0,114,0,236,0,0,0,166,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,148,0,0,210,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,134,0,18,0,0,0,0,0,66,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,252,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,227,0,0,49,0,0,0,0,177,0,0,99,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,47,0,0,0,0,0,0,0,0,0,0,175,0,0,0,101,0,0,0,0,229,0,0,0,0,0,0,0,0,245,63,0,0,0,0,0,0,191,117,0,0,0,0,0,0,150,0,0,0,0,0,0,0,0,0,0,0,0,0,132,0,0,0,0,0,0,97,159,0,0,0,0,31,225,0,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,180,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,0,222,160,0,0,143,0,0,0,247,0,0,0,145,0,0,119,0,254,0,17,0,0,0,0,0,0,0,0,0,0,224,0,0,0,0,0,0,204,0,240,0,0,103,0,0,0,0,0,0,0,0,0,0,231,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,241,0,0,0,0,0,0,0,0,0,0,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,0,0,0,0,0,0,0,238,0,1,0,0,0,0,0,0,0,0,0,0,129,19,0,0,0,0,0,0,0,0,0,0,147,0,0,164,0,0,0,0,0,0,0,0,0,0,0,0,0,206,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,220,0,0,0,0,0,0,0,0,0,211,0,110,0,0,83,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,0,0,45,0,0,0,0,173,0,0,85,0,176,0,0,0,61,0,52,0,0,0,0,0,0,189,0,0,0,0,0,32,94,131,0,0,0,197,0,0,3,0,0,0,69,0,0,126,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,195,0,96,76,0,0,0,0,0,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,182,0,0,0,0,0,0,0,124,0,0,0,0,0,0,0,0,0,0,0,0,71,0,0,0,0,0,0,0,0,199,0,0,0,0,0,0,0,0,87,0,0,0,0,215,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,29,0,0,0,0,0,0,35,0,0,0,157,163,0,0,0,0,0,0,193,0,0,0,0,65,0,0,0,0,0,0,0,0,0,0,0,4,0,141,0,0,0,22,0,0,13,0,0,0,0,162,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,226,0,0,0,0,0,0,108,0,242,0,0,0,0,0,0,0,50,0,0,0,0,0,0,192,0,0,38,0,0,0,0,0,0,0,0,82,0,0,209,0,0,0,0,128,0,0,20,81,0,0,0,0,0,0,146,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,130,0,0,194,0,51,0,144,0,0,0,0,0,0,179,0,0,0,0,0,0,0,0,0,250,0,0,0,0,0,0,0,58,0,0,0,0,0,0,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,105,0,0,0,234,184,0,0,172,233,0,0,0,0,0,0,170,0,190,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,74,0,84,10,0,0,0,0,0,0,0,0,0,158,0,0,0,120,0,0,0,0,26,0,0,25,0,0,0,0,0,0,0,0,153,0,104,0,0,0,0,218,0,0,0,0,0,0,0,0,0,0,0,0,135,249,0,0,0,0,121,7,0,0,0,0,0,0,0,0,0,0,60,0,0,0,0,0,46,0,0,0,0,0,0,0,0,0,23,0,0,0,0,0,0,0,0,0,0,151,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,137,0,0,0,111,9,0,0,0,239,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,142,0,0,196,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,255,0,0,0,0,0,0,0,0,127,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,0,0,0,0,70,0,169,0,0,0,123,0,0,0,0,0,0,216,0,251,0,0,0,0,116,0,0,0,140,0,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,0,55,253,0,0,0,102,0,0,125,183,0,0,0,0,0,0,0,0,39,0,0,0,0,167,0,0,0,109,0,0,0,0,0,0,0,0,0,0,237,0,8,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,214,0,57,0,0,235,0,0,0,0,107,0,0,185,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,156,0,0,0,0,0,0,0,0,118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,228,0,0,0,0,0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,73,0,0,0,0,0,0,0,0,0,0,201,43,0,0,0,0,28,0,0,0,0,0,171,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,246,0,0,0,0,0,0,0,223,0,0,0,0,0,200,0,0,0,0,95,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,198,0,207,0,0,0,0,0,0,79,0,0,0,0,0,0,0,0,0,88,244,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,12,0,133,0,0,0,0,0,0,230,59,0,0,0,0,0,0,187,0,152,0,0,0,0,0,0,0,0,0,0,89,0,0,0,0,0,0,217,0,0,0,0,0,149,0,0,136,0,21,0,0,0,0,0,0,0,0,77,0,0,0,0,0,0,0,0,205,0,0,0,0,0,0,174,0,0,0,0,53,0,0,0,0,0,0,181,0,188,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,0,0,93,0,0,0,155,221,0,0,165,27,0,0,0,91,0,0,0,0,0,0,0,0,0,0,219,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,0,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,186,0,0,0,0,0,0,0,122,0,11,0,0,0,0,0,0,168,0,139,0,0,0,0,0,0,56,106,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,62,0,42,0,0,0,0,0,138,212,0,202,0,0,0,0,0,0,0,0,0,0,30,0,0,0,248,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,154,0,0,0,0,0,0,0,0,75,0,0,0,0,0,0,203,0,232,0,0,90,0]
private theorem fingerprint_leftInverse : ∀ n : Fin 256,
    inverseCodes[fingerprint (table n)]! = n.val := by decide +kernel
private theorem table_injective : Function.Injective table := by
  intro n k he
  apply Fin.ext
  rw [←fingerprint_leftInverse n,←fingerprint_leftInverse k,he]
private theorem K_card_lower : 256 ≤ Nat.card K := by
  let f : Fin 256 → K := fun n => ⟨⟨elements n,(elements_mem n).1⟩,(elements_mem n).2⟩
  have hi : Function.Injective f := by
    intro n k he
    apply table_injective
    rw [←elements_matrix,←elements_matrix]
    exact congrArg (fun x : K => ((x.val.val : Matrix12ˣ) : Matrix12)) he
  simpa using Nat.card_le_card_of_injective f hi
private def repWords : Fin 9 → List (Fin 7) := ![[],[4],[5],[6],[4,5],[5,3],[5,6],[4,5,3],[5,3,4]]
private def rep (i : Fin 9) : actionGroup := ((repWords i).map gen).prod
private theorem rep_mem (i : Fin 9) : rep i ∈ H :=
  H.list_prod_mem (by intro g hg; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg; exact gen_mem j)
private def next : Fin 9 → Fin 7 → Fin 9 := ![![0,0,0,0,1,2,3],![1,1,3,3,3,4,0],![2,2,2,5,4,0,6],![3,3,1,1,0,6,1],![4,4,6,7,6,1,2],![5,5,5,2,8,5,7],![6,6,4,8,2,3,4],![7,7,8,4,5,7,8],![8,8,7,6,7,8,5]]
private theorem rep_zero : rep 0 = 1 := rfl
private def decode (a : Array ℕ) : Matrix12 := Thompson.BinaryMatrix.decode 12 a
private def mulRows (a b : Array ℕ) : Array ℕ :=
  #[Thompson.BinaryMatrix.rowProduct a[0]! b 12,
    Thompson.BinaryMatrix.rowProduct a[1]! b 12,
    Thompson.BinaryMatrix.rowProduct a[2]! b 12,
    Thompson.BinaryMatrix.rowProduct a[3]! b 12,
    Thompson.BinaryMatrix.rowProduct a[4]! b 12,
    Thompson.BinaryMatrix.rowProduct a[5]! b 12,
    Thompson.BinaryMatrix.rowProduct a[6]! b 12,
    Thompson.BinaryMatrix.rowProduct a[7]! b 12,
    Thompson.BinaryMatrix.rowProduct a[8]! b 12,
    Thompson.BinaryMatrix.rowProduct a[9]! b 12,
    Thompson.BinaryMatrix.rowProduct a[10]! b 12,
    Thompson.BinaryMatrix.rowProduct a[11]! b 12]
private theorem decode_mulRows (a b : Array ℕ) : decode (mulRows a b) = decode a * decode b := by
  symm
  apply Thompson.BinaryMatrix.decode_mul
  intro i
  fin_cases i <;> rfl
private def genRows : Fin 7 → Array ℕ := ![#[509,1513,4,256,148,164,64,128,8,624,147,3095],#[916,1735,1130,556,1265,175,858,922,1505,1761,1818,3781],#[1310,1382,1376,558,1530,174,1913,678,786,654,1217,2671],#[916,1735,1129,558,472,174,1648,14,1432,38,1888,3819],#[1533,1919,3296,1102,3735,278,3833,2183,1086,3449,1390,3810],#[58,1309,1307,1324,2397,2413,1451,116,315,2893,2153,3536],#[1532,1917,3300,1094,3719,310,3769,2055,1342,3961,366,1762]]
private def repRows : Fin 9 → Array ℕ := ![#[1,2,4,8,16,32,64,128,256,512,1024,2048],#[1533,1919,3296,1102,3735,278,3833,2183,1086,3449,1390,3810],#[58,1309,1307,1324,2397,2413,1451,116,315,2893,2153,3536],#[1532,1917,3300,1094,3719,310,3769,2055,1342,3961,366,1762],#[3248,660,2315,2280,2017,2144,3597,3480,3443,1039,190,1883],#[1439,1779,1117,1041,2312,2174,1317,879,915,2294,2447,2997],#[3210,1929,3088,3524,3772,269,2982,3564,3144,3906,2263,2699],#[2291,1433,3086,2581,1946,2101,3198,4075,3654,1140,504,523],#[3436,874,2131,3588,3730,75,2395,3204,3541,3202,2167,2494]]
private def repInvRows : Fin 9 → Array ℕ := ![#[1,2,4,8,16,32,64,128,256,512,1024,2048],#[1532,1917,3300,1094,3719,310,3769,2055,1342,3961,366,1762],#[58,1309,1307,1324,2397,2413,1451,116,315,2893,2153,3536],#[1533,1919,3296,1102,3735,278,3833,2183,1086,3449,1390,3810],#[3210,1929,3088,3524,3772,269,2982,3564,3144,3906,2263,2699],#[1604,1735,441,1802,2197,3123,1727,1322,1367,2411,3801,589],#[3248,660,2315,2280,2017,2144,3597,3480,3443,1039,190,1883],#[3146,1740,818,2066,2426,2748,898,1629,2571,2708,374,3230],#[2574,11,651,3864,495,1679,1341,887,3932,1023,4015,3795]]
private def basisRows : Array ℕ := #[293,100,1842,192,1072,768,1704,1696,128,1024,512,2048]
private def basisInvRows : Array ℕ := #[1323,52,1674,192,1424,1920,264,256,1056,1024,512,2048]
private theorem gen_decode (i : Fin 7) : ((gen i : Matrix12ˣ) : Matrix12) = decode (genRows i) := by
  revert i
  decide +kernel
private theorem rep_decode (i : Fin 9) : ((rep i : Matrix12ˣ) : Matrix12) = decode (repRows i) := by
  revert i
  decide +kernel
private def repUnit (i : Fin 9) : Matrix12ˣ where
  val := decode (repRows i)
  inv := decode (repInvRows i)
  val_inv := by
    apply Thompson.BinaryMatrix.decode_mul_one
    revert i
    decide +kernel
  inv_val := by
    apply Thompson.BinaryMatrix.decode_mul_one
    revert i
    decide +kernel
private theorem rep_inv_decode (i : Fin 9) : (((rep i)⁻¹ : Matrix12ˣ) : Matrix12) = decode (repInvRows i) := by
  have he : (rep i : Matrix12ˣ) = repUnit i := Units.ext (rep_decode i)
  change (((rep i : Matrix12ˣ)⁻¹ : Matrix12ˣ) : Matrix12) = _
  rw [he]
  rfl
private theorem basis_decode : basis = decode basisRows := by decide +kernel
private theorem basisInv_decode : basisInv = decode basisInvRows := by decide +kernel
private theorem transitions (i : Fin 9) (j : Fin 7) :
    rep i * gen j * (rep (next i j))⁻¹ ∈ lower := by
  change (basisInv * ((((rep i : Matrix12ˣ) : Matrix12) * ((gen j : Matrix12ˣ) : Matrix12)) *
    (((rep (next i j))⁻¹ : Matrix12ˣ) : Matrix12)) * basis).BlockTriangular
    (OrderDual.toDual : Fin 12 → OrderDual (Fin 12))
  rw [rep_decode,gen_decode,rep_inv_decode,basis_decode,basisInv_decode]
  simp only [←decode_mulRows]
  revert i j
  decide +kernel
private theorem distinct_reps (i j : Fin 9) (h : rep i * (rep j)⁻¹ ∈ lower) : i = j := by
  change (basisInv * (((rep i : Matrix12ˣ) : Matrix12) * (((rep j)⁻¹ : Matrix12ˣ) : Matrix12)) *
    basis).BlockTriangular (OrderDual.toDual : Fin 12 → OrderDual (Fin 12)) at h
  rw [rep_decode,rep_inv_decode,basis_decode,basisInv_decode] at h
  simp only [←decode_mulRows] at h
  have hh : ∀ i j : Fin 9,
      (decode (mulRows (mulRows basisInvRows (mulRows (repRows i) (repInvRows j))) basisRows)).BlockTriangular
        (OrderDual.toDual : Fin 12 → OrderDual (Fin 12)) → i = j := by
    decide +kernel
  exact hh i j h
private theorem cover (g : actionGroup) (hg : g ∈ H) :
    ∃ i k, k ∈ H ∧ k ∈ lower ∧ g = k * rep i := by
  have step (g : actionGroup) (hg : g ∈ H) (j : Fin 7)
      (he : ∃ i k, k ∈ H ∧ k ∈ lower ∧ g = k * rep i) :
      ∃ i k, k ∈ H ∧ k ∈ lower ∧ g * gen j = k * rep i := by
    obtain ⟨i,k,hk,hl,rfl⟩ := he
    let a := rep i * gen j * (rep (next i j))⁻¹
    refine ⟨next i j,k*a,H.mul_mem hk (H.mul_mem (H.mul_mem (rep_mem i) (gen_mem j))
      (H.inv_mem (rep_mem _))),lower.mul_mem hl (transitions i j),?_⟩
    simp only [a,mul_assoc,inv_mul_cancel,mul_one]
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0,1,H.one_mem,lower.one_mem,by simp [rep_zero]⟩
  | mul_right x hx y hy ih =>
    obtain ⟨j,rfl⟩ := hy
    exact step x hx j ih
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨j,rfl⟩ := hy
    rw [←gen_inv]
    exact step x hx (inverseIndex j) ih
private theorem H_card : Nat.card H = Nat.card K * 9 := by
  let f : K × Fin 9 → H := fun x => ⟨x.1.val.val * rep x.2,H.mul_mem x.1.val.property (rep_mem _)⟩
  have hi : Function.Injective f := by
    rintro ⟨k,i⟩ ⟨l,j⟩ he
    have hv : k.val.val * rep i = l.val.val * rep j := congrArg (fun x : H => x.val) he
    have hr : rep i * (rep j)⁻¹ = k.val.val⁻¹ * l.val.val := by
      apply mul_inv_eq_iff_eq_mul.mpr
      rw [mul_assoc]
      exact eq_inv_mul_iff_mul_eq.mpr hv
    have hij : i = j := distinct_reps i j (hr.symm ▸ lower.mul_mem (lower.inv_mem k.property) l.property)
    subst j
    have hkl : k = l := Subtype.ext (Subtype.ext (mul_right_cancel hv))
    exact Prod.ext hkl rfl
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨i,k,hk,hl,he⟩ := cover x x.property
    exact ⟨(⟨⟨k,hk⟩,hl⟩,i),Subtype.ext he.symm⟩
  simpa using (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm
private theorem ambient_card : Nat.card actionGroup = 2661120 := by
  have he : Nat.card coverSubgroup = Nat.card M22TripleCover :=
    Nat.card_congr (subgroupOfEquivOfLe derivedGroup_le_actionGroup).toEquiv
  have hc := coverSubgroup.card_mul_index
  rw [he,M22TripleCover.card,coverSubgroup_index] at hc
  exact hc.symm
private theorem K_card : Nat.card K = 256 := by
  obtain ⟨P,hP⟩ := lower_two.exists_le_sylow
  have hupper : Nat.card K ≤ Nat.card lower :=
    Nat.card_le_card_of_injective
      (fun x : K => (⟨x.val.val,x.property⟩ : lower))
      (fun x y he => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : lower => (z : actionGroup)) he)
  have hpc : Nat.card P = 256 := by
    rw [P.card_eq_multiplicity,ambient_card]
    decide +kernel
  have hu : Nat.card lower ≤ 256 := (card_le_of_le hP).trans_eq hpc
  exact Nat.le_antisymm (hupper.trans hu) K_card_lower
private theorem H_solvable : Group.IsSolvable H := by
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [H_card,K_card] at hd
  have hn : 256 * 9 = 2 ^ 8 * 3 ^ 2 := by decide
  rw [hn] at hd
  rcases hp.dvd_mul.mp hd with hh | hh
  · exact Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp (hp.dvd_of_dvd_pow hh)).resolve_left hp.ne_one)
  · exact Or.inr (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow hh)).resolve_left hp.ne_one)
private def R : Subgroup actionGroup := K.map H.subtype
private theorem R_card : Nat.card R = 256 := by
  change Nat.card (K.map H.subtype) = 256
  rw [Nat.card_congr (equivMapOfInjective K H.subtype H.subtype_injective).toEquiv.symm,K_card]
private def P : Sylow 2 actionGroup := Sylow.ofCard R (by rw [ambient_card,R_card]; decide +kernel)
private theorem P_le : (P : Subgroup actionGroup) ≤ H := by
  exact (Subgroup.map_le_range H.subtype K).trans_eq H.range_subtype
private def v0 : M22TripleCover.BinarySpace := fun i => if i = 11 then 1 else 0
private theorem v0_ne : v0 ≠ 0 := by decide +kernel
private theorem table_fixed : ∀ n : Fin 256, table n *ᵥ v0 = v0 := by decide +kernel
private theorem P_fixed : v0 ∈ fixedSpace binaryAction (P : Subgroup actionGroup) := by
  intro g
  obtain ⟨k,hk,he⟩ := g.property
  let kk : K := ⟨k,hk⟩
  let f : Fin 256 → K := fun n => ⟨⟨elements n,(elements_mem n).1⟩,(elements_mem n).2⟩
  have hi : Function.Injective f := by
    intro n k he
    apply table_injective
    rw [←elements_matrix,←elements_matrix]
    exact congrArg (fun x : K => ((x.val.val : Matrix12ˣ) : Matrix12)) he
  have hs : Function.Surjective f := (hi.bijective_of_nat_card_le (by rw [K_card,Nat.card_fin])).2
  obtain ⟨n,hn⟩ := hs kk
  have hv : (elements n : actionGroup) = g := (congrArg (fun x : K => x.val.val) hn).trans he
  change (((g.val : actionGroup) : Matrix12ˣ) : Matrix12) *ᵥ v0 = v0
  rw [←hv,elements_matrix,table_fixed]
private theorem scalar_eq_gen : scalarElement = gen 4 := by
  apply Subtype.ext
  apply Units.ext
  change (scalarUnit : Matrix12) = matrices 4
  rw [coe_scalarUnit]
  decide +kernel
private theorem scalar_le : scalarSubgroup ≤ H := by
  rw [scalarSubgroup_eq_zpowers]
  exact zpowers_le.mpr (scalar_eq_gen.symm ▸ gen_mem 4)
/-- The scalar orbit span of a vector in the actual binary cover module. -/
def scalarSpan (v : M22TripleCover.BinarySpace) : Submodule (ZMod 2) M22TripleCover.BinarySpace :=
  Submodule.span (ZMod 2) (Set.range (fun z : scalarSubgroup => binaryAction z v))
private def plane : Submodule (ZMod 2) M22TripleCover.BinarySpace :=
  Submodule.span (ZMod 2) ({v0,binaryAction scalarElement v0} : Set M22TripleCover.BinarySpace)
private theorem scalarSpan_le_plane : scalarSpan v0 ≤ plane := by
  apply Submodule.span_le.mpr
  rintro _ ⟨z,rfl⟩
  change binaryAction (z : actionGroup) v0 ∈ plane
  have hz : z.val ∈ zpowers scalarElement := scalarSubgroup_eq_zpowers ▸ z.property
  obtain ⟨i,hi,hzi⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hz)
  have hi := Finset.mem_range.mp hi
  rw [scalarElement_order] at hi
  interval_cases i
  · rw [←hzi,pow_zero,map_one,Module.End.one_apply]
    exact Submodule.subset_span (Or.inl rfl)
  · rw [←hzi,pow_one]
    exact Submodule.subset_span (Or.inr rfl)
  · rw [←hzi]
    have he : binaryAction (scalarElement ^ 2) v0 = v0 + binaryAction scalarElement v0 := by
      rw [scalar_eq_gen]
      decide +kernel
    rw [he]
    exact plane.add_mem (Submodule.subset_span (Or.inl rfl)) (Submodule.subset_span (Or.inr rfl))
private theorem moves_plane : binaryAction (gen 5) v0 ∉ plane := by
  intro hm
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hm
  have h : ∀ a b : ZMod 2,
      a • v0 + b • binaryAction scalarElement v0 ≠ binaryAction (gen 5) v0 := by
    rw [scalar_eq_gen]
    decide +kernel
  exact h a b he
private theorem initial_escape :
    ∃ D : Subgroup actionGroup, Group.IsSolvable D ∧ scalarSubgroup ⊔ (P : Subgroup actionGroup) ≤ D ∧
      ∃ v : M22TripleCover.BinarySpace, v ≠ 0 ∧ v ∈ fixedSpace binaryAction (P : Subgroup actionGroup) ∧
        ∃ x ∈ D, binaryAction x v ∉ scalarSpan v := by
  exact ⟨H,H_solvable,sup_le scalar_le P_le,v0,v0_ne,P_fixed,gen 5,gen_mem 5,
    fun hv => moves_plane (scalarSpan_le_plane hv)⟩
private theorem scalarSpan_conjugate (g : actionGroup) (v w : M22TripleCover.BinarySpace)
    (hw : w ∈ scalarSpan v) : binaryAction g w ∈ scalarSpan (binaryAction g v) := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z,rfl⟩ := hy
    have hz : g * (z : actionGroup) * g⁻¹ ∈ scalarSubgroup :=
      (inferInstance : scalarSubgroup.Normal).conj_mem (z : actionGroup) z.property g
    have he : binaryAction g (binaryAction z v) =
        binaryAction (g * (z : actionGroup) * g⁻¹) (binaryAction g v) := by
      simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
    rw [he]
    exact Submodule.subset_span ⟨⟨_,hz⟩,rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (scalarSpan (binaryAction g v)).add_mem ihx ihy
  | smul a x hx ih => simpa using (scalarSpan (binaryAction g v)).smul_mem a ih
/-- Every Sylow two-subgroup of the literal covering extension has a solvable
scalar overgroup which moves the scalar plane on its fixed line. -/
theorem exists_solvable_escape (S : Sylow 2 actionGroup) :
    ∃ D : Subgroup actionGroup, Group.IsSolvable D ∧ scalarSubgroup ⊔ (S : Subgroup actionGroup) ≤ D ∧
      ∃ v : M22TripleCover.BinarySpace, v ≠ 0 ∧ v ∈ fixedSpace binaryAction (S : Subgroup actionGroup) ∧
        ∃ x ∈ D, binaryAction x v ∉ scalarSpan v := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq actionGroup P S
  have hS : (g • P : Sylow 2 actionGroup).toSubgroup =
      (P : Subgroup actionGroup).map (MulAut.conj g).toMonoidHom := by
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    have he : (MulDistribMulAction.toMonoidEnd (MulAut actionGroup) actionGroup) (MulAut.conj g) =
        (MulAut.conj g).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      rfl
    exact congrArg (fun f : actionGroup →* actionGroup => (P : Subgroup actionGroup).map f) he
  obtain ⟨D,hd,hB,v,hv,hfix,x,hx,hmove⟩ := initial_escape
  let f := (MulAut.conj g).toMonoidHom
  let D' := D.map f
  have hs : Group.IsSolvable D' := by
    let := hd
    exact Group.isSolvable_of_surjective
      (f := (equivMapOfInjective D f (MulAut.conj g).injective).toMonoidHom)
      (equivMapOfInjective D f (MulAut.conj g).injective).surjective
  have hinv (w : M22TripleCover.BinarySpace) : binaryAction g⁻¹ (binaryAction g w) = w := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  refine ⟨D',hs,sup_le ?_ ?_,binaryAction g v,?_,?_,f x,mem_map_of_mem f hx,?_⟩
  · intro z hz
    have hi : g⁻¹*z*g ∈ scalarSubgroup := by
      simpa only [inv_inv] using (inferInstance : scalarSubgroup.Normal).conj_mem z hz g⁻¹
    refine ⟨g⁻¹*z*g,(le_sup_left.trans hB) hi,?_⟩
    simp [f,MulAut.conj_apply,mul_assoc]
  · rw [hS]
    exact map_mono (le_sup_right.trans hB)
  · intro he
    have hh := congrArg (fun w => binaryAction g⁻¹ w) he
    rw [hinv,map_zero] at hh
    exact hv hh
  · intro s
    have hm : (s : actionGroup) ∈ (P : Subgroup actionGroup).map (MulAut.conj g).toMonoidHom := by
      simpa only [hS] using s.property
    obtain ⟨y,hy,hey⟩ := hm
    change binaryAction (s : actionGroup) (binaryAction g v) = binaryAction g v
    rw [←hey]
    change binaryAction (g*y*g⁻¹) (binaryAction g v) = _
    have hyfix : binaryAction y v = v := hfix ⟨y,hy⟩
    rw [map_mul,map_mul]
    simp only [Module.End.mul_apply,hinv,hyfix]
  · intro hm
    have hh := scalarSpan_conjugate g⁻¹ (binaryAction g v) _ hm
    rw [hinv] at hh
    apply hmove
    change binaryAction g⁻¹ (binaryAction (g*x*g⁻¹) (binaryAction g v)) ∈ scalarSpan v at hh
    simpa only [map_mul,Module.End.mul_apply,hinv] using hh
end Sporadic.Mathieu.M22TripleCover.Escape
