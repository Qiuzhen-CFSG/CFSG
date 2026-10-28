module
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.WordCertificate
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.FastHexads
/-! Completeness of the short-word normalizer certificate, checked using the
two integer hexad codes and then transported to actual M₁₂ membership. -/
@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
def parameterCode (a : NormalizerParameters) : Nat :=
  (3 * (a.1 0).val + (a.1 1).val) * 512 +
  (a.2.1 0 0).val + 2 * (a.2.1 1 0).val + 4 * (a.2.1 2 0).val +
  8 * (a.2.2 (0,0) 0).val + 16 * (a.2.2 (0,1) 0).val +
  32 * (a.2.2 (1,0) 0).val + 64 * (a.2.2 (1,1) 0).val +
  128 * (a.2.2 (2,0) 0).val + 256 * (a.2.2 (2,1) 0).val

/-- A suggested word index for each admissible coordinate code. The table is
untrusted data: `parameter_word_check` verifies every suggested equality. -/
def wordIndexTable : List (Nat × Fin 192) := [
  (512,0),
  (992,32),
  (920,38),
  (632,6),
  (980,112),
  (564,144),
  (588,150),
  (940,118),
  (658,33),
  (882,1),
  (778,7),
  (746,39),
  (710,113),
  (806,145),
  (862,151),
  (702,119),
  (705,40),
  (801,8),
  (857,10),
  (697,42),
  (661,120),
  (885,152),
  (781,154),
  (749,122),
  (979,41),
  (563,9),
  (587,11),
  (939,43),
  (519,153),
  (999,121),
  (927,123),
  (639,155),
  (1408,50),
  (1120,66),
  (1048,70),
  (1528,54),
  (1108,178),
  (1460,162),
  (1484,166),
  (1068,182),
  (1298,67),
  (1266,51),
  (1162,55),
  (1386,71),
  (1350,179),
  (1190,163),
  (1246,167),
  (1342,183),
  (1345,72),
  (1185,56),
  (1241,60),
  (1337,76),
  (1301,184),
  (1269,168),
  (1165,172),
  (1389,188),
  (1107,73),
  (1459,57),
  (1483,61),
  (1067,77),
  (1415,169),
  (1127,185),
  (1055,189),
  (1535,173),
  (1920,34),
  (1632,2),
  (1560,4),
  (2040,36),
  (1620,146),
  (1972,114),
  (1996,116),
  (1580,148),
  (1810,3),
  (1778,35),
  (1674,37),
  (1898,5),
  (1862,147),
  (1702,115),
  (1758,117),
  (1854,149),
  (1857,12),
  (1697,44),
  (1753,46),
  (1849,14),
  (1813,156),
  (1781,124),
  (1677,126),
  (1901,158),
  (1619,13),
  (1971,45),
  (1995,47),
  (1579,15),
  (1927,125),
  (1639,157),
  (1567,159),
  (2047,127),
  (2560,84),
  (3040,20),
  (2968,22),
  (2680,86),
  (3028,100),
  (2612,132),
  (2636,134),
  (2988,102),
  (2706,21),
  (2930,85),
  (2826,87),
  (2794,23),
  (2758,101),
  (2854,133),
  (2910,135),
  (2750,103),
  (2753,28),
  (2849,92),
  (2905,94),
  (2745,30),
  (2709,108),
  (2933,140),
  (2829,142),
  (2797,110),
  (3027,29),
  (2611,93),
  (2635,95),
  (2987,31),
  (2567,141),
  (3047,109),
  (2975,111),
  (2687,143),
  (3072,68),
  (3552,52),
  (3480,48),
  (3192,64),
  (3540,164),
  (3124,180),
  (3148,176),
  (3500,160),
  (3218,53),
  (3442,69),
  (3338,65),
  (3306,49),
  (3270,165),
  (3366,181),
  (3422,177),
  (3262,161),
  (3265,58),
  (3361,74),
  (3417,78),
  (3257,62),
  (3221,170),
  (3445,186),
  (3341,190),
  (3309,174),
  (3539,59),
  (3123,75),
  (3147,79),
  (3499,63),
  (3079,187),
  (3559,171),
  (3487,175),
  (3199,191),
  (3968,18),
  (3680,82),
  (3608,80),
  (4088,16),
  (3668,130),
  (4020,98),
  (4044,96),
  (3628,128),
  (3858,83),
  (3826,19),
  (3722,17),
  (3946,81),
  (3910,131),
  (3750,99),
  (3806,97),
  (3902,129),
  (3905,88),
  (3745,24),
  (3801,26),
  (3897,90),
  (3861,136),
  (3829,104),
  (3725,106),
  (3949,138),
  (3667,89),
  (4019,25),
  (4043,27),
  (3627,91),
  (3975,105),
  (3687,137),
  (3615,139),
  (4095,107)
]

def parameterWordIndex (a : NormalizerParameters) : Fin 192 :=
  ((wordIndexTable.find? (fun pair => pair.1 == parameterCode a)).map Prod.snd).getD 0

theorem parameter_word_check : ∀ a : NormalizerParameters,
    FastHexadCheck (normalizerParameterPerm a) →
      (wordElement (parameterWordIndex a)).val = normalizerParameterPerm a := by
  decide +kernel

theorem parameter_word_exists : ∀ a : NormalizerParameters,
    FastHexadCheck (normalizerParameterPerm a) →
      ∃ i : Fin 192, (wordElement i).val = normalizerParameterPerm a := by
  intro a ha
  exact ⟨parameterWordIndex a,parameter_word_check a ha⟩

theorem parameter_in_wordCarrier (a : NormalizerParameters)
    (ha : TwoHexadCheck (normalizerParameterPerm a)) :
    normalizerParameterPerm a ∈ wordCarrier := by
  obtain ⟨i,hi⟩ := parameter_word_exists a (twoHexadCheck_fast _ ha)
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩

theorem mem_wordCarrier_iff (p : Equiv.Perm (Fin 12)) :
    p ∈ wordCarrier ↔ PreservesM12Blocks p ∧ NormalizesPlanePerms p := by
  constructor
  · intro hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(mem_M12_iff_preservesBlocks _).mp (wordElement i).property,
      (mem_secondParabolic_iff _).mp (wordElement_mem i)⟩
  · intro hp
    obtain ⟨a,_,ha⟩ := Finset.mem_map.mp (normalizerSymmetricCarrier_complete p hp.2)
    change normalizerParameterPerm a = p at ha
    rw [← ha]
    apply parameter_in_wordCarrier
    rw [ha]
    exact preserves_twoHexads p hp.1

end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
