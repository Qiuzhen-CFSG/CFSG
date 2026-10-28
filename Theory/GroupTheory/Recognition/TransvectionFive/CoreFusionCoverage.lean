module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceInvolutions
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceInvolutions
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylow
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylowCensus

/-!
# Point-centralizer fusion of its involutions into the two rectangles

The standard Sylow has 192 square-one elements. For each, a short packed
matrix certificate supplies an invertible conjugator that fixes the marked
transvection and carries the element into one of the two literal rectangular
subgroups. The checker verifies inverses, intertwining and point fixation;
its soundness is ordinary matrix multiplication over the binary field.
Sylow conjugacy extends the result to the whole centralizer, and the original
marking transports both the conjugator and the subgroup memberships.

This is the local involution placement used in Aschbacher, *Sporadic Groups*
(1994), 39.8, pp.215–216. It is independent of ambient fusion counts. The
internal imports reuse the checked Sylow encoding and packed matrix bridge.
The certificate table is irreducible to avoid expanding its cases during
abstract proof elaboration; its computational checker remains kernel-checked.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.CoreFusionCoverage
open UniquenessLinear UniquenessLinear.SylowCoordinates Thompson.BinaryMatrix

@[irreducible] private def coverageCertificate : ℕ → (BitVec 10) × Array ℕ × Array ℕ
  | 0 => (0, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 1 => (2, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 2 => (2, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 3 => (2, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 4 => (4, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 5 => (4, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 6 => (6, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 7 => (6, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 8 => (8, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 9 => (10, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 10 => (10, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 11 => (10, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 12 => (12, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 13 => (12, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 14 => (14, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 15 => (14, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 16 => (16, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 18 => (18, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 20 => (20, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 22 => (22, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 24 => (24, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 26 => (26, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 28 => (28, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 30 => (30, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 32 => (32, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 34 => (34, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 36 => (36, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 38 => (38, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 40 => (40, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 42 => (42, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 44 => (44, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 46 => (46, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 48 => (48, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 50 => (50, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 52 => (52, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 54 => (54, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 56 => (56, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 58 => (58, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 60 => (60, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 62 => (62, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 64 => (64, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 66 => (66, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 68 => (68, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 70 => (70, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 72 => (72, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 74 => (74, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 76 => (76, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 78 => (78, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 80 => (80, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 82 => (82, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 84 => (84, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 86 => (86, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 88 => (88, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 90 => (90, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 92 => (92, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 94 => (94, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 96 => (96, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 98 => (98, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 100 => (100, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 102 => (102, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 104 => (104, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 106 => (106, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 108 => (108, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 110 => (110, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 112 => (112, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 114 => (114, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 116 => (116, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 118 => (118, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 120 => (120, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 122 => (122, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 124 => (124, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 126 => (126, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 128 => (128, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 129 => (34, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 132 => (132, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 133 => (38, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 136 => (136, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 137 => (42, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 140 => (140, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 141 => (46, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 160 => (160, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 163 => (34, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 164 => (164, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 167 => (38, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 168 => (168, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 171 => (42, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 172 => (172, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 175 => (46, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 192 => (192, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 196 => (196, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 200 => (200, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 204 => (204, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 224 => (224, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 228 => (228, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 232 => (232, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 236 => (236, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 256 => (256, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 257 => (66, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 260 => (260, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 261 => (260, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 264 => (264, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 265 => (74, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 268 => (268, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 269 => (268, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 288 => (288, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 292 => (292, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 296 => (296, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 300 => (300, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 320 => (320, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 323 => (66, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 324 => (324, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 327 => (70, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 328 => (328, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 331 => (74, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 332 => (332, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 335 => (78, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 352 => (352, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 356 => (356, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 360 => (360, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 364 => (364, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 384 => (384, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 385 => (98, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 388 => (388, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 389 => (102, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 392 => (392, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 393 => (106, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 396 => (396, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 397 => (110, #[1, 4, 6, 8, 16], #[1, 6, 2, 8, 16])
  | 416 => (416, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 420 => (420, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 424 => (424, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 428 => (428, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 448 => (448, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 452 => (452, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 456 => (456, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 460 => (460, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 480 => (480, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 483 => (98, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 484 => (484, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 487 => (102, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 488 => (488, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 491 => (106, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 492 => (492, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])
  | 495 => (110, #[1, 2, 6, 8, 16], #[1, 2, 6, 8, 16])
  | 512 => (64, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 513 => (68, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 514 => (66, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 515 => (70, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 520 => (72, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 521 => (76, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 522 => (74, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 523 => (78, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 528 => (288, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 530 => (292, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 536 => (296, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 538 => (300, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 576 => (64, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 578 => (66, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 581 => (68, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 583 => (70, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 584 => (72, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 586 => (74, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 589 => (76, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 591 => (78, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 592 => (352, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 594 => (356, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 600 => (360, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 602 => (364, #[1, 2, 8, 12, 16], #[1, 2, 12, 4, 16])
  | 768 => (256, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 769 => (324, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 774 => (260, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 775 => (260, #[1, 2, 4, 14, 16], #[1, 2, 4, 14, 16])
  | 776 => (264, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 777 => (332, #[1, 8, 4, 10, 16], #[1, 10, 4, 2, 16])
  | 782 => (268, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 783 => (268, #[1, 2, 4, 14, 16], #[1, 2, 4, 14, 16])
  | 816 => (288, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 822 => (292, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 824 => (296, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 830 => (300, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 832 => (320, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 835 => (66, #[1, 2, 6, 10, 16], #[1, 2, 6, 10, 16])
  | 837 => (324, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 838 => (324, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 840 => (328, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 843 => (74, #[1, 2, 6, 10, 16], #[1, 2, 6, 10, 16])
  | 845 => (332, #[1, 2, 4, 10, 16], #[1, 2, 4, 10, 16])
  | 846 => (332, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 880 => (352, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 886 => (356, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 888 => (360, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | 894 => (364, #[1, 2, 4, 12, 16], #[1, 2, 4, 12, 16])
  | _ => (0, #[1, 2, 4, 8, 16], #[1, 2, 4, 8, 16])

private def coverageCheck (a : BitVec 10) : Bool :=
  let (b,q,qi) := coverageCertificate a.toNat
  (rect2 b || rect3 b) && (List.range 5).all (fun i =>
    decide (rowProduct q[i]! qi 5 = 2^i) &&
    decide (rowProduct (packedUpper a)[i]! q 5 = rowProduct q[i]! (packedUpper b) 5) &&
    decide (rowProduct q[i]! #[17,2,4,8,16] 5 = rowProduct (#[17,2,4,8,16] : Array ℕ)[i]! q 5))

set_option maxRecDepth 4096 in
private theorem coverage_checked : involutionList.all coverageCheck = true := by decide +kernel

private theorem packed_rowProduct_eq (a b c d : Array ℕ)
    (h : ∀ i : Fin 5, rowProduct a[i.val]! b 5 = rowProduct c[i.val]! d 5) :
    decode 5 a * decode 5 b = decode 5 c * decode 5 d := by
  ext i j
  change (∑ k : Fin 5, Thompson.BinaryMatrix.bit a[i.val]! k.val * Thompson.BinaryMatrix.bit b[k.val]! j.val) =
    (∑ k : Fin 5, Thompson.BinaryMatrix.bit c[i.val]! k.val * Thompson.BinaryMatrix.bit d[k.val]! j.val)
  rw [Fin.sum_univ_eq_sum_range (fun k => Thompson.BinaryMatrix.bit a[i.val]! k * Thompson.BinaryMatrix.bit b[k]! j.val),
    Fin.sum_univ_eq_sum_range (fun k => Thompson.BinaryMatrix.bit c[i.val]! k * Thompson.BinaryMatrix.bit d[k]! j.val),
    ← bit_rowProduct, ← bit_rowProduct, h i]

private theorem coverage_spec (a : BitVec 10) (ha : square a = true) :
    let (b,q,qi) := coverageCertificate a.toNat
    (rect2 b = true ∨ rect3 b = true) ∧
    decode 5 q * decode 5 qi = 1 ∧
    decode 5 (packedUpper a) * decode 5 q = decode 5 q * decode 5 (packedUpper b) ∧
    decode 5 q * transvection.val = transvection.val * decode 5 q := by
  have hh := List.all_eq_true.mp coverage_checked a (square_mem a ha)
  simp only [coverageCheck,Bool.and_eq_true,Bool.or_eq_true] at hh
  have ht : transvection.val = decode 5 #[17,2,4,8,16] := by decide +kernel
  refine ⟨hh.1,decode_mul_one _ _ _ ?_,packed_rowProduct_eq _ _ _ _ ?_,?_⟩
  · intro i
    have hi := List.all_eq_true.mp hh.2 i.val (List.mem_range.mpr i.isLt)
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    exact hi.1.1
  · intro i
    have hi := List.all_eq_true.mp hh.2 i.val (List.mem_range.mpr i.isLt)
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    exact hi.1.2
  · rw [ht]
    apply packed_rowProduct_eq
    intro i
    have hi := List.all_eq_true.mp hh.2 i.val (List.mem_range.mpr i.isLt)
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    exact hi.2

private theorem packed_rectangle2 : ∀ b : BitVec 10, rect2 b = true →
    ∀ i j : Fin 5, ¬ (i.val < 2 ∧ 2 ≤ j.val) →
      decode 5 (packedUpper b) i j = if i = j then 1 else 0 := by
  unfold decode
  decide +kernel

private theorem packed_rectangle3 : ∀ b : BitVec 10, rect3 b = true →
    ∀ i j : Fin 5, ¬ (i.val < 3 ∧ 3 ≤ j.val) →
      decode 5 (packedUpper b) i j = if i = j then 1 else 0 := by
  unfold decode
  decide +kernel

/-- Every square-one element in the marked Sylow is conjugate into one
of its two rectangles by an element of the full point centralizer. -/
theorem upper_square_conjugate_rectangle (g : upper) (hg : (g : SL)^2 = 1) :
    ∃ c : centralizer,
      (c : SL)*(g : SL)*(c : SL)⁻¹ ∈ rectangle 2 ∨
      (c : SL)*(g : SL)*(c : SL)⁻¹ ∈ rectangle 3 := by
  have hs := coverage_spec (encode g) (square_encode g (by simpa only [pow_two] using hg))
  let b := (coverageCertificate (encode g).toNat).1
  let q : SL := ⟨decode 5 (coverageCertificate (encode g).toNat).2.1,
    det_one_of_right_inverse _ _ hs.2.1⟩
  have hq : q ∈ centralizer := mem_centralizer_singleton_iff.mpr (Subtype.ext hs.2.2.2)
  let r : SL := q⁻¹*(g : SL)*q
  have hr : r.val = decode 5 (packedUpper b) := by
    change q⁻¹.val * (g : SL).val * q.val = _
    rw [Matrix.mul_assoc,upper_matrix g]
    rw [show decode 5 (packedUpper (encode g)) * q.val = q.val * decode 5 (packedUpper b) from hs.2.2.1]
    rw [← Matrix.mul_assoc,show q⁻¹.val*q.val = 1 from congrArg Subtype.val (inv_mul_cancel q),Matrix.one_mul]
  refine ⟨⟨q⁻¹,centralizer.inv_mem hq⟩,?_⟩
  change q⁻¹*(g : SL)*(q⁻¹)⁻¹ ∈ rectangle 2 ∨ q⁻¹*(g : SL)*(q⁻¹)⁻¹ ∈ rectangle 3
  rw [inv_inv]
  change r ∈ rectangle 2 ∨ r ∈ rectangle 3
  rcases hs.1 with h | h
  · left
    apply (RectangleCoordinates.mem2_iff r).mpr
    intro i j hij
    rw [hr]
    exact packed_rectangle2 b h i j hij
  · right
    apply (RectangleCoordinates.mem3_iff r).mpr
    intro i j hij
    rw [hr]
    exact packed_rectangle3 b h i j hij

open Theory.SpecificGroups.LinearSylowNormalizers

/-- Sylow conjugacy keeps the rectangle conjugator inside the full model
point centralizer. -/
theorem centralizer_involution_conjugate_rectangle (q : centralizer) (hq : orderOf q = 2) :
    ∃ c : centralizer,
      (c : SL)*(q : SL)*(c : SL)⁻¹ ∈ rectangle 2 ∨
      (c : SL)*(q : SL)*(c : SL)⁻¹ ∈ rectangle 3 := by
  obtain ⟨y,hy⟩ := involution_into_sylow modelPointSylow q hq
  obtain ⟨d,hd⟩ := isConj_iff.mp hy
  have hyu : ((y : centralizer) : SL) ∈ upper := by
    have hh := y.property
    change ((y : centralizer) : SL) ∈ (standardSylow 5 (ZMod 2) (by decide) : Subgroup SL) at hh
    rw [coe_standardSylow,← model_upper_eq_unipotent] at hh
    exact hh
  have hyo : orderOf (y : centralizer) = 2 := by
    have he : MulAut.conj d q = (y : centralizer) := hd
    rw [← he,MulEquiv.orderOf_eq,hq]
  have hysq : (((y : centralizer) : SL))^2 = 1 := by
    have hh : (y : centralizer)^2 = 1 := by simpa only [hyo] using pow_orderOf_eq_one (y : centralizer)
    exact congrArg Subtype.val hh
  obtain ⟨c,hc⟩ := upper_square_conjugate_rectangle ⟨_,hyu⟩ hysq
  refine ⟨c*d,?_⟩
  have he : ((c*d : centralizer) : SL)*(q : SL)*((c*d : centralizer) : SL)⁻¹ =
      (c : SL)*((y : centralizer) : SL)*(c : SL)⁻¹ := by
    rw [← hd]
    simp only [Subgroup.coe_mul,Subgroup.coe_inv]
    group
  rw [he]
  exact hc

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- Every involution in the original point centralizer is conjugate into
one of its literal rectangles by an element of that same centralizer. -/
theorem marked_involution_conjugate_rectangle (q : G)
    (hq : q ∈ Subgroup.centralizer ({z} : Set G)) (ho : orderOf q = 2) :
    ∃ c : Subgroup.centralizer ({z} : Set G),
      (c : G)*q*(c : G)⁻¹ ∈ F.plane ∨ (c : G)*q*(c : G)⁻¹ ∈ F.threeSpace := by
  let qH : Subgroup.centralizer ({z} : Set G) := ⟨q,hq⟩
  have hoM : orderOf (F.equiv qH) = 2 :=
    (F.equiv.orderOf_eq qH).trans ((Subgroup.orderOf_coe qH).symm.trans ho)
  obtain ⟨c,hc⟩ := centralizer_involution_conjugate_rectangle (F.equiv qH) hoM
  let d := F.equiv.symm c
  refine ⟨d,?_⟩
  have he : F.equiv (d*qH*d⁻¹) = c*F.equiv qH*c⁻¹ := by
    simp only [map_mul,map_inv,d,F.equiv.apply_symm_apply]
  rcases hc with hc | hc
  · left
    apply (F.mem_pullback_iff Model.plane (d*qH*d⁻¹)).mpr
    rw [he]
    exact hc
  · right
    apply (F.mem_pullback_iff Model.threeSpace (d*qH*d⁻¹)).mpr
    rw [he]
    exact hc

end Theory.GroupTheory.TransvectionFive.CoreFusionCoverage
