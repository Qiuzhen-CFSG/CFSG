module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts.Common

/-!
# Complete X times Z cubed certificate

The sparse left factor uses Relations1242.check. Every coordinate hint
is checked; dense rows use the proved sequential XOR algorithm.
Source: ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2.
See `source/README.md`; bit j of row i is entry (i,j), without transposition.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

def xHints00 : List (Option Nat) := [some 3, some 2, some 6, some 7, none, none, some 11, some 12, none, some 10, some 18, some 19, some 21, some 5, some 15, some 27, some 17, some 30, some 31, some 33, some 8, some 37, some 9, some 24, some 43, some 26, some 46]
def xHints01 : List (Option Nat) := [some 47, some 29, some 51, some 52, some 54, some 13, some 58, some 14, some 36, some 64, some 65, some 16, some 40, some 71, some 42, some 74, some 75, some 45, some 79, some 80, some 82, some 20, some 50, some 88, some 89, some 91, some 22]
def xHints02 : List (Option Nat) := [some 95, some 23, some 57, some 101, some 102, some 25, some 61, some 108, some 63, some 111, some 112, some 114, some 28, some 68, some 120, some 70, some 123, some 124, some 73, some 128, some 129, some 131, some 32, some 78, some 137, some 138, some 140]
def xHints03 : List (Option Nat) := [some 34, some 144, some 35, some 85, some 150, some 87, some 153, some 154, some 156, some 38, some 160, some 39, some 94, some 166, some 167, some 41, some 98, some 173, some 100, some 176, some 177, some 179, some 44, some 105, some 185, some 107, some 188]
def xHints04 : List (Option Nat) := [some 189, some 110, some 193, some 194, some 196, some 48, some 200, some 49, some 117, some 206, some 119, some 209, some 210, some 122, some 214, some 215, some 217, some 53, some 127, some 223, some 224, some 226, some 55, some 230, some 56, some 134, some 236]
def xHints05 : List (Option Nat) := [some 136, some 239, some 240, some 242, some 59, some 246, some 60, some 143, some 252, some 253, some 62, some 147, some 259, some 149, some 262, some 263, some 152, some 267, some 268, some 270, some 66, some 274, some 67, some 159, some 280, some 281, some 69]
def xHints06 : List (Option Nat) := [some 163, some 287, some 165, some 290, some 291, some 293, some 72, some 170, some 299, some 172, some 302, some 303, some 175, some 307, some 308, some 310, some 76, some 314, some 77, some 182, some 320, some 184, some 323, some 324, some 187, some 328, some 329]
def xHints07 : List (Option Nat) := [some 331, some 81, some 192, some 337, some 338, some 340, some 83, some 344, some 84, some 199, some 350, some 351, some 86, some 203, some 357, some 205, some 360, some 361, some 208, some 365, some 366, some 368, some 90, some 213, some 374, some 375, some 377]
def xHints08 : List (Option Nat) := [some 92, some 381, some 93, some 220, some 387, some 222, some 390, some 391, some 393, some 96, some 397, some 97, some 229, some 403, some 404, some 99, some 233, some 410, some 235, some 413, some 414, some 238, some 418, some 419, some 421, some 103, some 425]
def xHints09 : List (Option Nat) := [some 104, some 245, some 431, some 432, some 106, some 249, some 438, some 251, some 441, some 442, some 444, some 109, some 256, some 450, some 258, some 453, some 454, some 261, some 458, some 459, some 461, some 113, some 266, some 467, some 468, some 470, some 115]
def xHints10 : List (Option Nat) := [some 474, some 116, some 273, some 480, some 481, some 118, some 277, some 487, some 279, some 490, some 491, some 493, some 121, some 284, some 498, some 286, some 501, some 502, some 289, some 506, some 507, some 509, some 125, some 513, some 126, some 296, some 519]
def xHints11 : List (Option Nat) := [some 298, some 522, some 523, some 301, some 527, some 528, some 530, some 130, some 306, some 536, some 537, some 539, some 132, some 543, some 133, some 313, some 549, some 550, some 135, some 317, some 556, some 319, some 559, some 560, some 322, some 564, some 565]
def xHints12 : List (Option Nat) := [some 567, some 139, some 327, some 573, some 574, some 576, some 141, some 580, some 142, some 334, some 586, some 336, some 589, some 590, some 592, some 145, some 596, some 146, some 343, some 602, some 603, some 148, some 347, some 609, some 349, some 612, some 613]
def xHints13 : List (Option Nat) := [some 615, some 151, some 354, some 621, some 356, some 624, some 625, some 359, some 629, some 630, some 632, some 155, some 364, some 638, some 639, some 641, some 157, some 645, some 158, some 371, some 651, some 373, some 654, some 655, some 657, some 161, some 660]
def xHints14 : List (Option Nat) := [some 162, some 380, some 666, some 667, some 164, some 384, some 673, some 386, some 676, some 677, some 389, some 681, some 682, some 684, some 168, some 688, some 169, some 396, some 694, some 695, some 171, some 400, some 701, some 402, some 704, some 705, some 707]
def xHints15 : List (Option Nat) := [some 174, some 407, some 713, some 409, some 716, some 717, some 412, some 721, some 722, some 724, some 178, some 417, some 730, some 731, some 733, some 180, some 737, some 181, some 424, some 743, some 744, some 183, some 428, some 749, some 430, some 752, some 753]
def xHints16 : List (Option Nat) := [some 755, some 186, some 435, some 759, some 437, some 762, some 763, some 440, some 767, some 768, some 770, some 190, some 774, some 191, some 447, some 780, some 449, some 783, some 784, some 452, some 788, some 789, some 791, some 195, some 457, some 797, some 798]
def xHints17 : List (Option Nat) := [some 800, some 197, some 804, some 198, some 464, some 810, some 466, some 813, some 814, some 816, some 201, some 820, some 202, some 473, some 826, some 827, some 204, some 477, some 833, some 479, some 836, some 837, some 839, some 207, some 484, some 844, some 486]
def xHints18 : List (Option Nat) := [some 847, some 848, some 489, some 852, some 853, some 855, some 211, some 859, some 212, some 496, some 865, none, some 868, some 500, some 872, some 873, some 875, some 216, some 505, some 881, some 882, some 884, some 218, some 888, some 219, some 512, some 894]
def xHints19 : List (Option Nat) := [some 895, some 221, some 516, some 901, some 518, some 904, some 905, some 521, none, some 909, some 911, some 225, some 526, some 917, some 918, some 920, some 227, some 924, some 228, some 533, some 930, some 535, some 933, some 934, some 936, some 231, some 940]
def xHints20 : List (Option Nat) := [some 232, some 542, some 945, some 946, some 234, some 546, some 952, some 548, some 955, some 956, some 958, some 237, some 553, some 964, some 555, some 967, some 968, some 558, some 972, some 973, some 975, some 241, some 563, some 981, none, some 983, some 243]
def xHints21 : List (Option Nat) := [some 986, some 244, some 570, some 992, some 572, some 995, some 996, none, some 247, some 1000, some 248, some 579, some 1006, some 1007, some 250, some 583, some 1013, some 585, some 1016, some 1017, some 588, some 1021, some 1022, some 1024, some 254, some 1028, some 255]
def xHints22 : List (Option Nat) := [some 595, some 1033, some 1034, some 257, some 599, some 1040, some 601, some 1043, some 1044, some 1046, some 260, some 606, some 1051, some 608, some 1054, some 1055, some 611, some 1059, some 1060, some 1062, some 264, some 1066, some 265, some 618, some 1072, some 620, some 1075]
def xHints23 : List (Option Nat) := [some 1076, some 623, some 1080, some 1081, some 1083, some 269, some 628, some 1089, some 1090, some 1092, some 271, some 1096, some 272, some 635, some 1102, some 637, some 1105, some 1106, some 1108, some 275, some 1111, some 276, some 644, some 1116, some 1117, some 278, some 648]
def xHints24 : List (Option Nat) := [some 1123, some 650, some 1126, some 1127, some 653, some 1131, some 1132, some 1134, some 282, some 1138, some 659, some 1141, some 1142, some 285, some 663, some 1148, some 665, some 1151, some 1152, some 1154, some 288, some 670, some 1160, some 672, some 1163, some 1164, some 675]
def xHints25 : List (Option Nat) := [some 1168, some 1169, some 1171, some 292, some 680, some 1177, some 1178, some 1180, some 294, some 1184, some 295, some 687, some 1190, some 1191, some 297, some 691, none, some 693, some 1197, some 1198, some 1200, some 300, some 698, some 1206, some 700, some 1209, some 1210]
def xHints26 : List (Option Nat) := [some 703, some 1214, some 1215, some 1217, some 304, some 1221, some 305, some 710, some 1227, some 712, some 1230, some 1231, some 715, some 1235, some 1236, some 1238, some 309, some 720, none, some 1241, none, some 311, none, some 312, some 727, none, some 729]
def xHints27 : List (Option Nat) := [none, none, none, some 315, none, some 316, some 736, none, none, some 318, some 740, none, some 742, none, none, none, some 321, none, some 748, none, none, some 751, none, none, none, some 325, none]
def xHints28 : List (Option Nat) := [some 326, some 758, none, none, some 761, none, none, none, some 330, some 766, none, none, none, some 332, none, some 333, some 773, none, none, some 335, some 777, none, some 779, none, none, some 782, some 497]
def xHints29 : List (Option Nat) := [none, none, some 339, some 787, none, none, none, some 341, none, some 342, some 794, none, some 796, none, none, none, some 345, none, some 346, some 803, none, none, some 348, some 807, none, some 809, none]
def xHints30 : List (Option Nat) := [none, some 812, none, none, none, some 352, none, some 353, some 819, none, none, some 355, some 823, none, some 825, none, none, none, some 358, some 830, none, some 832, none, none, some 835, none, none]
def xHints31 : List (Option Nat) := [none, some 362, none, some 363, some 842, none, none, none, some 846, none, none, none, some 367, some 851, none, none, none, some 369, none, some 370, some 858, none, none, some 372, some 862, none, some 864]
def xHints32 : List (Option Nat) := [none, none, some 867, some 448, none, some 376, some 871, none, none, none, some 378, none, some 379, some 878, none, some 880, none, none, none, some 382, none, some 383, some 887, none, none, some 385, some 891]
def xHints33 : List (Option Nat) := [none, some 893, none, none, none, some 388, some 898, none, some 900, none, none, some 903, none, none, none, some 392, some 908, none, none, some 394, none, some 395, some 914, none, some 916, none, none]
def xHints34 : List (Option Nat) := [none, some 398, none, some 399, some 923, none, none, some 401, some 927, none, some 929, none, none, some 932, none, none, none, some 405, none, some 406, some 939, none, none, some 408, some 943, none, none]
def xHints35 : List (Option Nat) := [none, none, some 411, some 949, none, some 951, none, none, some 954, none, none, none, some 415, none, some 416, some 961, none, some 963, none, none, some 966, none, none, none, some 420, some 971, none]
def xHints36 : List (Option Nat) := [none, none, some 422, none, some 423, some 978, none, some 980, none, none, some 426, none, some 427, none, none, some 429, some 989, none, some 991, none, none, some 994, none, none, none, some 433, some 999]
def xHints37 : List (Option Nat) := [none, none, some 436, some 1003, none, some 1005, none, none, none, some 439, some 1010, none, some 1012, none, none, some 1015, none, none, none, some 443, some 1020, none, none, none, some 445, none, some 446]
def xHints38 : List (Option Nat) := [some 1027, none, none, some 1030, some 711, some 1032, none, none, none, some 451, some 1037, none, some 1039, none, none, some 1042, none, none, none, some 455, none, some 456, some 1049, none, none, none, some 1053]
def xHints39 : List (Option Nat) := [none, none, none, some 460, some 1058, none, none, none, some 462, none, some 463, some 1065, none, none, some 465, some 1069, none, some 1071, none, none, some 1074, none, none, none, some 469, some 1079, none]
def xHints40 : List (Option Nat) := [none, none, some 471, none, some 472, some 1086, none, some 1088, none, none, none, some 475, none, some 476, some 1095, none, none, some 478, some 1099, none, some 1101, none, none, some 1104, none, none, none]
def xHints41 : List (Option Nat) := [some 482, none, some 1110, none, none, some 485, some 1114, none, none, none, none, some 488, some 1120, none, some 1122, none, none, some 1125, none, none, none, some 492, some 1130, none, none, none, some 494]
def xHints42 : List (Option Nat) := [none, some 495, some 1137, none, none, some 1140, none, none, none, some 499, some 1145, none, some 1147, none, none, some 1150, none, none, none, some 503, none, some 504, some 1157, none, some 1159, none, none]
def xHints43 : List (Option Nat) := [some 1162, none, none, none, some 508, some 1167, none, none, none, some 510, none, some 511, some 1174, none, some 1176, none, none, none, some 514, none, some 515, some 1183, none, none, some 517, some 1187, none]
def xHints44 : List (Option Nat) := [some 1189, none, none, none, some 520, some 1194, none, some 1196, none, none, none, some 524, none, some 525, some 1203, none, some 1205, none, none, some 1208, none, none, none, some 529, some 1213, none, none]
def xHints45 : List (Option Nat) := [none, some 531, none, some 532, some 1220, none, none, some 534, some 1224, none, some 1226, none, none, some 1229, some 593, none, none, some 538, some 1234, none, none, none, some 540, none, some 1240, none, none]
def xHints : List (Option Nat) := xHints00 ++ (xHints01 ++ (xHints02 ++ (xHints03 ++ (xHints04 ++ (xHints05 ++ (xHints06 ++ (xHints07 ++ (xHints08 ++ (xHints09 ++ (xHints10 ++ (xHints11 ++ (xHints12 ++ (xHints13 ++ (xHints14 ++ (xHints15 ++ (xHints16 ++ (xHints17 ++ (xHints18 ++ (xHints19 ++ (xHints20 ++ (xHints21 ++ (xHints22 ++ (xHints23 ++ (xHints24 ++ (xHints25 ++ (xHints26 ++ (xHints27 ++ (xHints28 ++ (xHints29 ++ (xHints30 ++ (xHints31 ++ (xHints32 ++ (xHints33 ++ (xHints34 ++ (xHints35 ++ (xHints36 ++ (xHints37 ++ (xHints38 ++ (xHints39 ++ (xHints40 ++ (xHints41 ++ (xHints42 ++ (xHints43 ++ (xHints44 ++ (xHints45)))))))))))))))))))))))))))))))))))))))))))))

set_option Elab.async false

set_option maxRecDepth 8192 in
private theorem product00 :
    check Data.x00 Data.z3Rows Data.t00 xHints00 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product01 :
    check Data.x01 Data.z3Rows Data.t01 xHints01 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product02 :
    check Data.x02 Data.z3Rows Data.t02 xHints02 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product03 :
    check Data.x03 Data.z3Rows Data.t03 xHints03 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product04 :
    check Data.x04 Data.z3Rows Data.t04 xHints04 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product05 :
    check Data.x05 Data.z3Rows Data.t05 xHints05 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product06 :
    check Data.x06 Data.z3Rows Data.t06 xHints06 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product07 :
    check Data.x07 Data.z3Rows Data.t07 xHints07 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product08 :
    check Data.x08 Data.z3Rows Data.t08 xHints08 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product09 :
    check Data.x09 Data.z3Rows Data.t09 xHints09 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product10 :
    check Data.x10 Data.z3Rows Data.t10 xHints10 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product11 :
    check Data.x11 Data.z3Rows Data.t11 xHints11 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product12 :
    check Data.x12 Data.z3Rows Data.t12 xHints12 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product13 :
    check Data.x13 Data.z3Rows Data.t13 xHints13 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product14 :
    check Data.x14 Data.z3Rows Data.t14 xHints14 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product15 :
    check Data.x15 Data.z3Rows Data.t15 xHints15 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product16 :
    check Data.x16 Data.z3Rows Data.t16 xHints16 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product17 :
    check Data.x17 Data.z3Rows Data.t17 xHints17 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product18 :
    check Data.x18 Data.z3Rows Data.t18 xHints18 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product19 :
    check Data.x19 Data.z3Rows Data.t19 xHints19 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product20 :
    check Data.x20 Data.z3Rows Data.t20 xHints20 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product21 :
    check Data.x21 Data.z3Rows Data.t21 xHints21 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product22 :
    check Data.x22 Data.z3Rows Data.t22 xHints22 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product23 :
    check Data.x23 Data.z3Rows Data.t23 xHints23 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product24 :
    check Data.x24 Data.z3Rows Data.t24 xHints24 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product25 :
    check Data.x25 Data.z3Rows Data.t25 xHints25 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product26 :
    check Data.x26 Data.z3Rows Data.t26 xHints26 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product27 :
    check Data.x27 Data.z3Rows Data.t27 xHints27 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product28 :
    check Data.x28 Data.z3Rows Data.t28 xHints28 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product29 :
    check Data.x29 Data.z3Rows Data.t29 xHints29 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product30 :
    check Data.x30 Data.z3Rows Data.t30 xHints30 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product31 :
    check Data.x31 Data.z3Rows Data.t31 xHints31 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product32 :
    check Data.x32 Data.z3Rows Data.t32 xHints32 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product33 :
    check Data.x33 Data.z3Rows Data.t33 xHints33 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product34 :
    check Data.x34 Data.z3Rows Data.t34 xHints34 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product35 :
    check Data.x35 Data.z3Rows Data.t35 xHints35 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product36 :
    check Data.x36 Data.z3Rows Data.t36 xHints36 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product37 :
    check Data.x37 Data.z3Rows Data.t37 xHints37 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product38 :
    check Data.x38 Data.z3Rows Data.t38 xHints38 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product39 :
    check Data.x39 Data.z3Rows Data.t39 xHints39 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product40 :
    check Data.x40 Data.z3Rows Data.t40 xHints40 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product41 :
    check Data.x41 Data.z3Rows Data.t41 xHints41 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product42 :
    check Data.x42 Data.z3Rows Data.t42 xHints42 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product43 :
    check Data.x43 Data.z3Rows Data.t43 xHints43 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product44 :
    check Data.x44 Data.z3Rows Data.t44 xHints44 = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem product45 :
    check Data.x45 Data.z3Rows Data.t45 xHints45 = true := by decide +kernel

private theorem part0 : check
    (Data.x00 ++ (Data.x01 ++ (Data.x02 ++ (Data.x03 ++ (Data.x04 ++ (Data.x05 ++ (Data.x06 ++ (Data.x07 ++ (Data.x08 ++ (Data.x09 ++ (Data.x10 ++ (Data.x11)))))))))))) Data.z3Rows
    (Data.t00 ++ (Data.t01 ++ (Data.t02 ++ (Data.t03 ++ (Data.t04 ++ (Data.t05 ++ (Data.t06 ++ (Data.t07 ++ (Data.t08 ++ (Data.t09 ++ (Data.t10 ++ (Data.t11))))))))))))
    (xHints00 ++ (xHints01 ++ (xHints02 ++ (xHints03 ++ (xHints04 ++ (xHints05 ++ (xHints06 ++ (xHints07 ++ (xHints08 ++ (xHints09 ++ (xHints10 ++ (xHints11)))))))))))) = true := by
  apply check_append
  · exact product00
  apply check_append
  · exact product01
  apply check_append
  · exact product02
  apply check_append
  · exact product03
  apply check_append
  · exact product04
  apply check_append
  · exact product05
  apply check_append
  · exact product06
  apply check_append
  · exact product07
  apply check_append
  · exact product08
  apply check_append
  · exact product09
  apply check_append
  · exact product10
  exact product11

private theorem part1 : check
    (Data.x12 ++ (Data.x13 ++ (Data.x14 ++ (Data.x15 ++ (Data.x16 ++ (Data.x17 ++ (Data.x18 ++ (Data.x19 ++ (Data.x20 ++ (Data.x21 ++ (Data.x22 ++ (Data.x23)))))))))))) Data.z3Rows
    (Data.t12 ++ (Data.t13 ++ (Data.t14 ++ (Data.t15 ++ (Data.t16 ++ (Data.t17 ++ (Data.t18 ++ (Data.t19 ++ (Data.t20 ++ (Data.t21 ++ (Data.t22 ++ (Data.t23))))))))))))
    (xHints12 ++ (xHints13 ++ (xHints14 ++ (xHints15 ++ (xHints16 ++ (xHints17 ++ (xHints18 ++ (xHints19 ++ (xHints20 ++ (xHints21 ++ (xHints22 ++ (xHints23)))))))))))) = true := by
  apply check_append
  · exact product12
  apply check_append
  · exact product13
  apply check_append
  · exact product14
  apply check_append
  · exact product15
  apply check_append
  · exact product16
  apply check_append
  · exact product17
  apply check_append
  · exact product18
  apply check_append
  · exact product19
  apply check_append
  · exact product20
  apply check_append
  · exact product21
  apply check_append
  · exact product22
  exact product23

private theorem part2 : check
    (Data.x24 ++ (Data.x25 ++ (Data.x26 ++ (Data.x27 ++ (Data.x28 ++ (Data.x29 ++ (Data.x30 ++ (Data.x31 ++ (Data.x32 ++ (Data.x33 ++ (Data.x34 ++ (Data.x35)))))))))))) Data.z3Rows
    (Data.t24 ++ (Data.t25 ++ (Data.t26 ++ (Data.t27 ++ (Data.t28 ++ (Data.t29 ++ (Data.t30 ++ (Data.t31 ++ (Data.t32 ++ (Data.t33 ++ (Data.t34 ++ (Data.t35))))))))))))
    (xHints24 ++ (xHints25 ++ (xHints26 ++ (xHints27 ++ (xHints28 ++ (xHints29 ++ (xHints30 ++ (xHints31 ++ (xHints32 ++ (xHints33 ++ (xHints34 ++ (xHints35)))))))))))) = true := by
  apply check_append
  · exact product24
  apply check_append
  · exact product25
  apply check_append
  · exact product26
  apply check_append
  · exact product27
  apply check_append
  · exact product28
  apply check_append
  · exact product29
  apply check_append
  · exact product30
  apply check_append
  · exact product31
  apply check_append
  · exact product32
  apply check_append
  · exact product33
  apply check_append
  · exact product34
  exact product35

private theorem part3 : check
    (Data.x36 ++ (Data.x37 ++ (Data.x38 ++ (Data.x39 ++ (Data.x40 ++ (Data.x41 ++ (Data.x42 ++ (Data.x43 ++ (Data.x44 ++ (Data.x45)))))))))) Data.z3Rows
    (Data.t36 ++ (Data.t37 ++ (Data.t38 ++ (Data.t39 ++ (Data.t40 ++ (Data.t41 ++ (Data.t42 ++ (Data.t43 ++ (Data.t44 ++ (Data.t45))))))))))
    (xHints36 ++ (xHints37 ++ (xHints38 ++ (xHints39 ++ (xHints40 ++ (xHints41 ++ (xHints42 ++ (xHints43 ++ (xHints44 ++ (xHints45)))))))))) = true := by
  apply check_append
  · exact product36
  apply check_append
  · exact product37
  apply check_append
  · exact product38
  apply check_append
  · exact product39
  apply check_append
  · exact product40
  apply check_append
  · exact product41
  apply check_append
  · exact product42
  apply check_append
  · exact product43
  apply check_append
  · exact product44
  exact product45

theorem tProduct_check : check Data.xRows Data.z3Rows Data.tRows xHints = true := by
  have h := check_append _ _ _ _ _ _ _ part0
    (check_append _ _ _ _ _ _ _ part1
      (check_append _ _ _ _ _ _ _ part2 part3))
  simpa only [Data.xRows, Data.tRows, xHints, List.append_assoc] using h

theorem tProduct : Data.x * Data.z3 = Data.t :=
  product 1242 Data.xRows Data.z3Rows Data.tRows xHints
    Data.xRows_length Data.z3Rows_length tProduct_check

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts
