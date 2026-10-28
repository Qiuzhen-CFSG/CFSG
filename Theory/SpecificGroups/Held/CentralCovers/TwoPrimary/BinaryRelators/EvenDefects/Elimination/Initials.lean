module

public meta import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.WordLiteral
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Data

/-!
# Reusing the checked prefix and checking additional source inputs

Source: John Bray, ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
The producer supplies data only. All equality and tail checks run in the kernel.
-/

public section

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Initials
open Comparison Comparison.Replay

open Theory.GroupTheory.CosetEnumeration

private def source (r : Fin 14409) : Fact :=
  ⟨FaithfulPresentation.M1Cosets.Schreier.initialRelator r, [], initialMask r⟩

variable {E : Type*} [Group E] {z x y : E}

private theorem source_holds (h : Normalized z x y) (r : Fin 14409) :
    Holds (tails h) (symbolValue x y) (source r) := by
  simpa only [Holds, source, eval_nil, one_mul] using initialRelator_eval h r

private theorem previous (h : Normalized z x y) :
    ValidBefore (tails h) (symbolValue x y) Data.db 17223 := by
  intro i hi
  simpa only [Data.db, if_pos hi] using
    Comparison.Certificate.Block027.valid (Comparison.Initials.valid h) i hi

private def indices0 : List (Fin 14409) := [3, 22, 116, 135, 159, 177, 183, 258, 269, 283, 328, 351, 389, 455, 512, 611, 619, 703, 706, 744, 766, 769, 848, 901, 986, 1028, 1129, 1149, 1287, 1329, 1350, 1412, 1416, 1559, 1630, 1647, 1728, 1762, 1812, 1825, 1931, 1959, 1994, 2015, 2124, 2145, 2231, 2259, 2342, 2350, 2355, 2379, 2386, 2404, 2565, 2582, 2589, 2663, 2680, 2708, 2764, 2770, 2796, 2894]

private theorem checked0 : verifyInputs Data.db source 17223 indices0 = true := by decide +kernel

private theorem prefix0 (h : Normalized z x y) : ValidBefore (tails h) (symbolValue x y) Data.db 17287 :=
  verifyInputs_sound (source_holds h) (previous h) indices0 checked0

private def indices1 : List (Fin 14409) := [2901, 2908, 2910, 2938, 2980, 3009, 3044, 3058, 3167, 3169, 3186, 3363, 3492, 3569, 3674, 3699, 3751, 3764, 3828, 3898, 4038, 4175, 4297, 4385, 4518, 4682, 4689, 4868, 5025, 5078, 5081, 5088, 5123, 5172, 5179, 5368, 5372, 5571, 5794, 5795, 5900, 6012, 6040, 6103, 6124, 6345, 6404, 6460, 6628, 6761, 6968, 6971, 7150, 7160, 7314, 7328, 7430, 7538, 7566, 7587, 7643, 7818, 7930, 7965]

private theorem checked1 : verifyInputs Data.db source 17287 indices1 = true := by decide +kernel

private theorem prefix1 (h : Normalized z x y) : ValidBefore (tails h) (symbolValue x y) Data.db 17351 :=
  verifyInputs_sound (source_holds h) (prefix0 h) indices1 checked1

private def indices2 : List (Fin 14409) := [8028, 8063, 8364, 8417, 8578, 8728, 8770, 8889, 8924, 9008, 9022, 9187, 9218, 9260, 9400, 9512, 9582, 9593, 9596, 9603, 9701, 9708, 9736, 9764, 10013, 10121, 10142, 10163, 10251, 10286, 10422, 10562, 10590, 10594, 10625, 10709, 10835, 10975, 10996, 11171, 11185, 11206, 11227, 11332, 11353, 11374, 11605, 11640, 11651, 11675, 11696, 11700, 11983, 12088, 12102, 12109, 12162, 12165, 12214, 12326, 12417, 12435, 12445, 12872]

private theorem checked2 : verifyInputs Data.db source 17351 indices2 = true := by decide +kernel

private theorem prefix2 (h : Normalized z x y) : ValidBefore (tails h) (symbolValue x y) Data.db 17415 :=
  verifyInputs_sound (source_holds h) (prefix1 h) indices2 checked2

private def indices3 : List (Fin 14409) := [12879, 12900, 12914, 12928, 12949, 12988, 13047, 13096, 13215, 13243, 13362, 13394, 13502, 13509, 13768, 13817, 13992, 14069, 14125, 14202, 14251, 14384, 68, 79, 971, 1882, 1888, 2488, 3884, 6660, 10349, 10531, 10569]

private theorem checked3 : verifyInputs Data.db source 17415 indices3 = true := by decide +kernel

private theorem prefix3 (h : Normalized z x y) : ValidBefore (tails h) (symbolValue x y) Data.db 17448 :=
  verifyInputs_sound (source_holds h) (prefix2 h) indices3 checked3

theorem valid (h : Normalized z x y) :
    ValidBefore (tails h) (symbolValue x y) Data.db Data.initialCount := prefix3 h

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Elimination.Initials
