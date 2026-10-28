module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic

/-!
# Literal first product in the mixed-word circuit

Checked row blocks certify AB = X on the untransposed ATLAS arrays.
Coordinate hints are verified by Relations1242.check; all other rows use
the proved sequential XOR computation. See source/README.md.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords

def hints00 : List (Option Nat) := [some 1, some 0, some 4, some 5, some 2, some 3, some 8, some 9, some 6, some 7, some 13, some 14, some 16, some 10, some 11, some 20, some 12, some 22, some 23, some 25, some 15, some 28, some 17, some 18, some 32, some 19, some 34]
def hints01 : List (Option Nat) := [some 35, some 21, some 38, some 39, some 41, some 24, some 44, some 26, some 27, some 48, some 49, some 29, some 30, some 53, some 31, some 55, some 56, some 33, some 59, some 60, some 62, some 36, some 37, some 66, some 67, some 69, some 40]
def hints02 : List (Option Nat) := [some 72, some 42, some 43, some 76, some 77, some 45, some 46, some 81, some 47, some 83, some 84, some 86, some 50, some 51, some 90, some 52, some 92, some 93, some 54, some 96, some 97, some 99, some 57, some 58, some 103, some 104, some 106]
def hints03 : List (Option Nat) := [some 61, some 109, some 63, some 64, some 113, some 65, some 115, some 116, some 118, some 68, some 121, some 70, some 71, some 125, some 126, some 73, some 74, some 130, some 75, some 132, some 133, some 135, some 78, some 79, some 139, some 80, some 141]
def hints04 : List (Option Nat) := [some 142, some 82, some 145, some 146, some 148, some 85, some 151, some 87, some 88, some 155, some 89, some 157, some 158, some 91, some 161, some 162, some 164, some 94, some 95, some 168, some 169, some 171, some 98, some 174, some 100, some 101, some 178]
def hints05 : List (Option Nat) := [some 102, some 180, some 181, some 183, some 105, some 186, some 107, some 108, some 190, some 191, some 110, some 111, some 195, some 112, some 197, some 198, some 114, some 201, some 202, some 204, some 117, some 207, some 119, some 120, some 211, some 212, some 122]
def hints06 : List (Option Nat) := [some 123, some 216, some 124, some 218, some 219, some 221, some 127, some 128, some 225, some 129, some 227, some 228, some 131, some 231, some 232, some 234, some 134, some 237, some 136, some 137, some 241, some 138, some 243, some 244, some 140, some 247, some 248]
def hints07 : List (Option Nat) := [some 250, some 143, some 144, some 254, some 255, some 257, some 147, some 260, some 149, some 150, some 264, some 265, some 152, some 153, some 269, some 154, some 271, some 272, some 156, some 275, some 276, some 278, some 159, some 160, some 282, some 283, some 285]
def hints08 : List (Option Nat) := [some 163, some 288, some 165, some 166, some 292, some 167, some 294, some 295, some 297, some 170, some 300, some 172, some 173, some 304, some 305, some 175, some 176, some 309, some 177, some 311, some 312, some 179, some 315, some 316, some 318, some 182, some 321]
def hints09 : List (Option Nat) := [some 184, some 185, some 325, some 326, some 187, some 188, some 330, some 189, some 332, some 333, some 335, some 192, some 193, some 339, some 194, some 341, some 342, some 196, some 345, some 346, some 348, some 199, some 200, some 352, some 353, some 355, some 203]
def hints10 : List (Option Nat) := [some 358, some 205, some 206, some 362, some 363, some 208, some 209, some 367, some 210, some 369, some 370, some 372, some 213, some 214, some 376, some 215, some 378, some 379, some 217, some 382, some 383, some 385, some 220, some 388, some 222, some 223, some 392]
def hints11 : List (Option Nat) := [some 224, some 394, some 395, some 226, some 398, some 399, some 401, some 229, some 230, some 405, some 406, some 408, some 233, some 411, some 235, some 236, some 415, some 416, some 238, some 239, some 420, some 240, some 422, some 423, some 242, some 426, some 427]
def hints12 : List (Option Nat) := [some 429, some 245, some 246, some 433, some 434, some 436, some 249, some 439, some 251, some 252, some 443, some 253, some 445, some 446, some 448, some 256, some 451, some 258, some 259, some 455, some 456, some 261, some 262, some 460, some 263, some 462, some 463]
def hints13 : List (Option Nat) := [some 465, some 266, some 267, some 469, some 268, some 471, some 472, some 270, some 475, some 476, some 478, some 273, some 274, some 482, some 483, some 485, some 277, some 488, some 279, some 280, some 492, some 281, some 494, some 495, some 497, some 284, some 499]
def hints14 : List (Option Nat) := [some 286, some 287, some 503, some 504, some 289, some 290, some 508, some 291, some 510, some 511, some 293, some 514, some 515, some 517, some 296, some 520, some 298, some 299, some 524, some 525, some 301, some 302, some 529, some 303, some 531, some 532, some 534]
def hints15 : List (Option Nat) := [some 306, some 307, some 538, some 308, some 540, some 541, some 310, some 544, some 545, some 547, some 313, some 314, some 551, some 552, some 554, some 317, some 557, some 319, some 320, some 561, some 562, some 322, some 323, some 566, some 324, some 568, some 569]
def hints16 : List (Option Nat) := [some 571, some 327, some 328, some 575, some 329, some 577, some 578, some 331, some 581, some 582, some 584, some 334, some 587, some 336, some 337, some 591, some 338, some 593, some 594, some 340, some 597, some 598, some 600, some 343, some 344, some 604, some 605]
def hints17 : List (Option Nat) := [some 607, some 347, some 610, some 349, some 350, some 614, some 351, some 616, some 617, some 619, some 354, some 622, some 356, some 357, some 626, some 627, some 359, some 360, some 631, some 361, some 633, some 634, some 636, some 364, some 365, some 640, some 366]
def hints18 : List (Option Nat) := [some 642, some 643, some 368, some 646, some 647, some 649, some 371, some 652, some 373, some 374, some 656, some 375, some 658, some 377, some 661, some 662, some 664, some 380, some 381, some 668, some 669, some 671, some 384, some 674, some 386, some 387, some 678]
def hints19 : List (Option Nat) := [some 679, some 389, some 390, some 683, some 391, some 685, some 686, some 393, some 689, some 690, some 692, some 396, some 397, some 696, some 697, some 699, some 400, some 702, some 402, some 403, some 706, some 404, some 708, some 709, some 711, some 407, some 714]
def hints20 : List (Option Nat) := [some 409, some 410, some 718, some 719, some 412, some 413, some 723, some 414, some 725, some 726, some 728, some 417, some 418, some 732, some 419, some 734, some 735, some 421, some 738, some 739, some 741, some 424, some 425, some 745, none, some 747, some 428]
def hints21 : List (Option Nat) := [some 750, some 430, some 431, some 754, some 432, some 756, some 757, none, some 435, some 760, some 437, some 438, some 764, some 765, some 440, some 441, some 769, some 442, some 771, some 772, some 444, some 775, some 776, some 778, some 447, some 781, some 449]
def hints22 : List (Option Nat) := [some 450, some 785, some 786, some 452, some 453, some 790, some 454, some 792, some 793, some 795, some 457, some 458, some 799, some 459, some 801, some 802, some 461, some 805, some 806, some 808, some 464, some 811, some 466, some 467, some 815, some 468, some 817]
def hints23 : List (Option Nat) := [some 818, some 470, some 821, some 822, some 824, some 473, some 474, some 828, some 829, some 831, some 477, some 834, some 479, some 480, some 838, some 481, some 840, some 841, some 843, some 484, some 845, some 486, some 487, some 849, some 850, some 489, some 490]
def hints24 : List (Option Nat) := [some 854, some 491, some 856, some 857, some 493, some 860, some 861, some 863, some 496, some 866, some 498, some 869, some 870, some 500, some 501, some 874, some 502, some 876, some 877, some 879, some 505, some 506, some 883, some 507, some 885, some 886, some 509]
def hints25 : List (Option Nat) := [some 889, some 890, some 892, some 512, some 513, some 896, some 897, some 899, some 516, some 902, some 518, some 519, some 906, some 907, some 521, some 522, some 910, some 523, some 912, some 913, some 915, some 526, some 527, some 919, some 528, some 921, some 922]
def hints26 : List (Option Nat) := [some 530, some 925, some 926, some 928, some 533, some 931, some 535, some 536, some 935, some 537, some 937, some 938, some 539, some 941, some 942, some 944, some 542, some 543, some 947, some 948, some 950, some 546, some 953, some 548, some 549, some 957, some 550]
def hints27 : List (Option Nat) := [some 959, some 960, some 962, some 553, some 965, some 555, some 556, some 969, some 970, some 558, some 559, some 974, some 560, some 976, some 977, some 979, some 563, some 982, some 565, some 984, none, some 567, some 987, some 988, some 990, some 570, some 993]
def hints28 : List (Option Nat) := [some 572, some 573, some 997, some 998, some 576, some 1001, some 1002, some 1004, some 579, some 580, some 1008, some 1009, some 1011, some 583, some 1014, some 585, some 586, some 1018, some 1019, some 588, some 589, some 1023, some 590, some 1025, some 1026, some 592, some 867]
def hints29 : List (Option Nat) := [some 1029, some 1031, some 595, some 596, some 1035, some 1036, some 1038, some 599, some 1041, some 601, some 602, some 1045, some 603, some 1047, some 1048, none, some 606, some 1052, some 608, some 609, some 1056, some 1057, some 611, some 612, some 1061, some 613, some 1063]
def hints30 : List (Option Nat) := [some 1064, some 615, some 1067, some 1068, some 1070, some 618, some 1073, some 620, some 621, some 1077, some 1078, some 623, some 624, some 1082, some 625, some 1084, some 1085, some 1087, some 628, some 629, some 1091, some 630, some 1093, some 1094, some 632, some 1097, some 1098]
def hints31 : List (Option Nat) := [some 1100, some 635, some 1103, some 637, some 638, some 1107, some 639, some 1109, some 641, some 1112, some 1113, some 1115, some 644, some 645, some 1118, some 1119, some 1121, some 648, some 1124, some 650, some 651, some 1128, some 1129, some 653, some 654, some 1133, some 655]
def hints32 : List (Option Nat) := [some 1135, some 1136, some 657, some 782, some 1139, some 659, some 660, some 1143, some 1144, some 1146, some 663, some 1149, some 665, some 666, some 1153, some 667, some 1155, some 1156, some 1158, some 670, some 1161, some 672, some 673, some 1165, some 1166, some 675, some 676]
def hints33 : List (Option Nat) := [some 1170, some 677, some 1172, some 1173, some 1175, some 680, some 681, some 1179, some 682, some 1181, some 1182, some 684, some 1185, some 1186, some 1188, some 687, some 688, some 1192, some 1193, some 691, some 1195, some 693, some 694, some 1199, some 695, some 1201, some 1202]
def hints34 : List (Option Nat) := [some 1204, some 698, some 1207, some 700, some 701, some 1211, some 1212, some 703, some 704, some 1216, some 705, some 1218, some 1219, some 707, some 1222, some 1223, some 1225, some 710, some 1228, some 712, some 713, some 1232, some 1233, some 715, some 716, some 1237, some 717]
def hints35 : List (Option Nat) := [some 1239, none, some 720, some 721, none, some 722, none, none, some 724, none, none, none, some 727, none, some 729, some 730, none, some 731, none, none, some 733, none, none, none, some 736, some 737, none]
def hints36 : List (Option Nat) := [none, none, some 740, none, some 742, some 743, none, some 744, none, none, some 746, none, some 748, none, none, some 751, some 752, none, some 753, none, none, some 755, none, none, none, some 758, some 759]
def hints37 : List (Option Nat) := [none, none, some 761, some 762, none, some 763, none, none, none, some 766, some 767, none, some 768, none, none, some 770, none, none, none, some 773, some 774, none, none, none, some 777, none, some 779]
def hints38 : List (Option Nat) := [some 780, none, none, some 783, some 1229, some 784, none, none, none, some 787, some 788, none, some 789, none, none, some 791, none, none, none, some 794, none, some 796, some 797, none, none, none, some 800]
def hints39 : List (Option Nat) := [none, none, none, some 803, some 804, none, none, none, some 807, none, some 809, some 810, none, none, some 812, some 813, none, some 814, none, none, some 816, none, none, none, some 819, some 820, none]
def hints40 : List (Option Nat) := [none, none, some 823, none, some 825, some 826, none, some 827, none, none, none, some 830, none, some 832, some 833, none, none, some 835, some 836, none, some 837, none, none, some 839, none, none, none]
def hints41 : List (Option Nat) := [some 842, none, some 844, none, none, some 846, some 847, none, some 848, none, none, some 851, some 852, none, some 853, none, none, some 855, none, none, none, some 858, some 859, none, none, none, some 862]
def hints42 : List (Option Nat) := [none, some 864, some 865, none, none, some 868, none, none, none, some 871, some 872, none, some 873, none, none, some 875, none, none, none, some 878, none, some 880, some 881, none, some 882, none, none]
def hints43 : List (Option Nat) := [some 884, none, none, none, some 887, some 888, none, none, none, some 891, none, some 893, some 894, none, some 895, none, none, none, some 898, none, some 900, some 901, none, none, some 903, some 904, none]
def hints44 : List (Option Nat) := [some 905, none, none, none, some 908, some 909, none, some 911, none, none, none, some 914, none, some 916, some 917, none, some 918, none, none, some 920, none, none, none, some 923, some 924, none, none]
def hints45 : List (Option Nat) := [none, some 927, none, some 929, some 930, none, none, some 932, some 933, none, some 934, none, none, some 936, some 1030, none, none, some 939, some 940, none, none, none, some 943, none, some 945, none, none]
def hints : List (Option Nat) := hints00 ++ (hints01 ++ (hints02 ++ (hints03 ++ (hints04 ++ (hints05 ++ (hints06 ++ (hints07 ++ (hints08 ++ (hints09 ++ (hints10 ++ (hints11 ++ (hints12 ++ (hints13 ++ (hints14 ++ (hints15 ++ (hints16 ++ (hints17 ++ (hints18 ++ (hints19 ++ (hints20 ++ (hints21 ++ (hints22 ++ (hints23 ++ (hints24 ++ (hints25 ++ (hints26 ++ (hints27 ++ (hints28 ++ (hints29 ++ (hints30 ++ (hints31 ++ (hints32 ++ (hints33 ++ (hints34 ++ (hints35 ++ (hints36 ++ (hints37 ++ (hints38 ++ (hints39 ++ (hints40 ++ (hints41 ++ (hints42 ++ (hints43 ++ (hints44 ++ (hints45)))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 8192 in
private theorem firstProduct_part0 :
    check (Data.a00 ++ (Data.a01 ++ (Data.a02 ++ (Data.a03 ++ (Data.a04 ++ (Data.a05 ++ (Data.a06 ++ (Data.a07 ++ (Data.a08 ++ (Data.a09 ++ (Data.a10 ++ (Data.a11)))))))))))) Data.bRows (Data.x00 ++ (Data.x01 ++ (Data.x02 ++ (Data.x03 ++ (Data.x04 ++ (Data.x05 ++ (Data.x06 ++ (Data.x07 ++ (Data.x08 ++ (Data.x09 ++ (Data.x10 ++ (Data.x11)))))))))))) (hints00 ++ (hints01 ++ (hints02 ++ (hints03 ++ (hints04 ++ (hints05 ++ (hints06 ++ (hints07 ++ (hints08 ++ (hints09 ++ (hints10 ++ (hints11)))))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem firstProduct_part1 :
    check (Data.a12 ++ (Data.a13 ++ (Data.a14 ++ (Data.a15 ++ (Data.a16 ++ (Data.a17 ++ (Data.a18 ++ (Data.a19 ++ (Data.a20 ++ (Data.a21 ++ (Data.a22 ++ (Data.a23)))))))))))) Data.bRows (Data.x12 ++ (Data.x13 ++ (Data.x14 ++ (Data.x15 ++ (Data.x16 ++ (Data.x17 ++ (Data.x18 ++ (Data.x19 ++ (Data.x20 ++ (Data.x21 ++ (Data.x22 ++ (Data.x23)))))))))))) (hints12 ++ (hints13 ++ (hints14 ++ (hints15 ++ (hints16 ++ (hints17 ++ (hints18 ++ (hints19 ++ (hints20 ++ (hints21 ++ (hints22 ++ (hints23)))))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem firstProduct_part2 :
    check (Data.a24 ++ (Data.a25 ++ (Data.a26 ++ (Data.a27 ++ (Data.a28 ++ (Data.a29 ++ (Data.a30 ++ (Data.a31 ++ (Data.a32 ++ (Data.a33 ++ (Data.a34 ++ (Data.a35)))))))))))) Data.bRows (Data.x24 ++ (Data.x25 ++ (Data.x26 ++ (Data.x27 ++ (Data.x28 ++ (Data.x29 ++ (Data.x30 ++ (Data.x31 ++ (Data.x32 ++ (Data.x33 ++ (Data.x34 ++ (Data.x35)))))))))))) (hints24 ++ (hints25 ++ (hints26 ++ (hints27 ++ (hints28 ++ (hints29 ++ (hints30 ++ (hints31 ++ (hints32 ++ (hints33 ++ (hints34 ++ (hints35)))))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

set_option maxRecDepth 8192 in
private theorem firstProduct_part3 :
    check (Data.a36 ++ (Data.a37 ++ (Data.a38 ++ (Data.a39 ++ (Data.a40 ++ (Data.a41 ++ (Data.a42 ++ (Data.a43 ++ (Data.a44 ++ (Data.a45)))))))))) Data.bRows (Data.x36 ++ (Data.x37 ++ (Data.x38 ++ (Data.x39 ++ (Data.x40 ++ (Data.x41 ++ (Data.x42 ++ (Data.x43 ++ (Data.x44 ++ (Data.x45)))))))))) (hints36 ++ (hints37 ++ (hints38 ++ (hints39 ++ (hints40 ++ (hints41 ++ (hints42 ++ (hints43 ++ (hints44 ++ (hints45)))))))))) = true := by
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  apply check_append
  · decide +kernel
  decide +kernel

theorem firstProduct_check : check Data.aRows Data.bRows Data.xRows hints = true := by
  have h := check_append _ _ _ _ _ _ _ firstProduct_part0
    (check_append _ _ _ _ _ _ _ firstProduct_part1
      (check_append _ _ _ _ _ _ _ firstProduct_part2 firstProduct_part3))
  simpa only [Data.aRows, Data.xRows, hints, List.append_assoc] using h

theorem first_product : Data1242.first * Data1242.second = Data.x := by
  rw [← Data.decode_aRows, ← Data.decode_bRows]
  exact product 1242 Data.aRows Data.bRows Data.xRows hints
    Data.aRows_length Data.bRows_length firstProduct_check

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
