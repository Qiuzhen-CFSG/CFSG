module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit.PairData
/-!
# Native Mathieu Sylow certificates

Kernel-checked decoding and distinctness of the native vector pairs. The fixed-size scalar certificates avoid repeated table lookup inside vector arithmetic.

These are the finite certificates for H.12.1(9) and 14.4.12, printed
pp.393–394 and 1011–1012. See `source/README.md` for data provenance.
-/

@[expose] public section
noncomputable section
open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender Subgroup
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
namespace SylowCertificates
open OrbitCertificates


theorem pair_decode : ∀ i, pairDecoder (pairCodes i) = i := by decide +kernel

theorem pairCodes_injective : Function.Injective pairCodes :=
  Function.LeftInverse.injective pair_decode

private theorem code_spec_0 : vectorCode (packed 1) + 4096 * vectorCode (packed 2) = 8193 := by decide +kernel
private theorem code_spec_1 : vectorCode (packed 3789) + 4096 * vectorCode (packed 3242) = 13283021 := by decide +kernel
private theorem code_spec_2 : vectorCode (packed 2802) + 4096 * vectorCode (packed 551) = 2259698 := by decide +kernel
private theorem code_spec_3 : vectorCode (packed 58) + 4096 * vectorCode (packed 2437) = 9982010 := by decide +kernel
private theorem code_spec_4 : vectorCode (packed 632) + 4096 * vectorCode (packed 1378) = 5644920 := by decide +kernel
private theorem code_spec_5 : vectorCode (packed 2802) + 4096 * vectorCode (packed 1459) = 5978866 := by decide +kernel
private theorem code_spec_6 : vectorCode (packed 1575) + 4096 * vectorCode (packed 1800) = 7374375 := by decide +kernel
private theorem code_spec_7 : vectorCode (packed 366) + 4096 * vectorCode (packed 2976) = 12190062 := by decide +kernel
private theorem code_spec_8 : vectorCode (packed 851) + 4096 * vectorCode (packed 1325) = 5428051 := by decide +kernel
private theorem code_spec_9 : vectorCode (packed 276) + 4096 * vectorCode (packed 1135) = 4649236 := by decide +kernel
private theorem code_spec_10 : vectorCode (packed 3122) + 4096 * vectorCode (packed 3675) = 15055922 := by decide +kernel
private theorem code_spec_11 : vectorCode (packed 275) + 4096 * vectorCode (packed 3727) = 15266067 := by decide +kernel
private theorem code_spec_12 : vectorCode (packed 2462) + 4096 * vectorCode (packed 3727) = 15268254 := by decide +kernel
private theorem code_spec_13 : vectorCode (packed 248) + 4096 * vectorCode (packed 4045) = 16568568 := by decide +kernel
private theorem code_spec_14 : vectorCode (packed 1) + 4096 * vectorCode (packed 1529) = 6262785 := by decide +kernel
private theorem code_spec_15 : vectorCode (packed 3038) + 4096 * vectorCode (packed 1325) = 5430238 := by decide +kernel
private theorem code_spec_16 : vectorCode (packed 2532) + 4096 * vectorCode (packed 320) = 1313252 := by decide +kernel
private theorem code_spec_17 : vectorCode (packed 2462) + 4096 * vectorCode (packed 2932) = 12011934 := by decide +kernel
private theorem code_spec_18 : vectorCode (packed 2531) + 4096 * vectorCode (packed 2976) = 12192227 := by decide +kernel
private theorem code_spec_19 : vectorCode (packed 3492) + 4096 * vectorCode (packed 1135) = 4652452 := by decide +kernel
private theorem code_spec_20 : vectorCode (packed 3421) + 4096 * vectorCode (packed 2976) = 12193117 := by decide +kernel
private theorem code_spec_21 : vectorCode (packed 3228) + 4096 * vectorCode (packed 3568) = 14617756 := by decide +kernel
private theorem code_spec_22 : vectorCode (packed 1659) + 4096 * vectorCode (packed 1135) = 4650619 := by decide +kernel
private theorem code_spec_23 : vectorCode (packed 366) + 4096 * vectorCode (packed 1529) = 6263150 := by decide +kernel
private theorem code_spec_24 : vectorCode (packed 248) + 4096 * vectorCode (packed 2741) = 11227384 := by decide +kernel
private theorem code_spec_25 : vectorCode (packed 3038) + 4096 * vectorCode (packed 1529) = 6265822 := by decide +kernel
private theorem code_spec_26 : vectorCode (packed 983) + 4096 * vectorCode (packed 2786) = 11412439 := by decide +kernel
private theorem code_spec_27 : vectorCode (packed 3869) + 4096 * vectorCode (packed 214) = 880413 := by decide +kernel
private theorem code_spec_28 : vectorCode (packed 2696) + 4096 * vectorCode (packed 1800) = 7375496 := by decide +kernel
private theorem code_spec_29 : vectorCode (packed 507) + 4096 * vectorCode (packed 3055) = 12513787 := by decide +kernel
private theorem code_spec_30 : vectorCode (packed 681) + 4096 * vectorCode (packed 2878) = 11788969 := by decide +kernel
private theorem code_spec_31 : vectorCode (packed 3221) + 4096 * vectorCode (packed 2437) = 9985173 := by decide +kernel
private theorem code_spec_32 : vectorCode (packed 514) + 4096 * vectorCode (packed 77) = 315906 := by decide +kernel
private theorem code_spec_33 : vectorCode (packed 1772) + 4096 * vectorCode (packed 156) = 640748 := by decide +kernel
private theorem code_spec_34 : vectorCode (packed 1629) + 4096 * vectorCode (packed 551) = 2258525 := by decide +kernel
private theorem code_spec_35 : vectorCode (packed 3487) + 4096 * vectorCode (packed 1378) = 5647775 := by decide +kernel
private theorem code_spec_36 : vectorCode (packed 681) + 4096 * vectorCode (packed 551) = 2257577 := by decide +kernel
private theorem code_spec_37 : vectorCode (packed 3239) + 4096 * vectorCode (packed 4010) = 16428199 := by decide +kernel
private theorem code_spec_38 : vectorCode (packed 4039) + 4096 * vectorCode (packed 1378) = 5648327 := by decide +kernel
private theorem code_spec_39 : vectorCode (packed 1686) + 4096 * vectorCode (packed 2878) = 11789974 := by decide +kernel
private theorem code_spec_40 : vectorCode (packed 3487) + 4096 * vectorCode (packed 3015) = 12352927 := by decide +kernel
private theorem code_spec_41 : vectorCode (packed 3708) + 4096 * vectorCode (packed 2878) = 11791996 := by decide +kernel
private theorem code_spec_42 : vectorCode (packed 985) + 4096 * vectorCode (packed 3776) = 15467481 := by decide +kernel
private theorem code_spec_43 : vectorCode (packed 1629) + 4096 * vectorCode (packed 3601) = 14751325 := by decide +kernel
private theorem code_spec_44 : vectorCode (packed 3852) + 4096 * vectorCode (packed 3776) = 15470348 := by decide +kernel
private theorem code_spec_45 : vectorCode (packed 58) + 4096 * vectorCode (packed 3601) = 14749754 := by decide +kernel
private theorem code_spec_46 : vectorCode (packed 610) + 4096 * vectorCode (packed 3242) = 13279842 := by decide +kernel
private theorem code_spec_47 : vectorCode (packed 3612) + 4096 * vectorCode (packed 3055) = 12516892 := by decide +kernel
private theorem code_spec_48 : vectorCode (packed 1686) + 4096 * vectorCode (packed 3242) = 13280918 := by decide +kernel
private theorem code_spec_49 : vectorCode (packed 3876) + 4096 * vectorCode (packed 295) = 1212196 := by decide +kernel
private theorem code_spec_50 : vectorCode (packed 3140) + 4096 * vectorCode (packed 3055) = 12516420 := by decide +kernel
private theorem code_spec_51 : vectorCode (packed 3789) + 4096 * vectorCode (packed 1459) = 5979853 := by decide +kernel
private theorem code_spec_52 : vectorCode (packed 632) + 4096 * vectorCode (packed 1354) = 5546616 := by decide +kernel
private theorem code_spec_53 : vectorCode (packed 1575) + 4096 * vectorCode (packed 1459) = 5977639 := by decide +kernel
private theorem code_spec_54 : vectorCode (packed 3799) + 4096 * vectorCode (packed 77) = 319191 := by decide +kernel
private theorem code_spec_55 : vectorCode (packed 139) + 4096 * vectorCode (packed 156) = 639115 := by decide +kernel
private theorem code_spec_56 : vectorCode (packed 872) + 4096 * vectorCode (packed 77) = 316264 := by decide +kernel
private theorem code_spec_57 : vectorCode (packed 3166) + 4096 * vectorCode (packed 1800) = 7375966 := by decide +kernel
private theorem code_spec_58 : vectorCode (packed 3636) + 4096 * vectorCode (packed 2693) = 11034164 := by decide +kernel
private theorem code_spec_59 : vectorCode (packed 304) + 4096 * vectorCode (packed 77) = 315696 := by decide +kernel
private theorem code_spec_60 : vectorCode (packed 2696) + 4096 * vectorCode (packed 3601) = 14752392 := by decide +kernel
private theorem code_spec_61 : vectorCode (packed 3852) + 4096 * vectorCode (packed 3816) = 15634188 := by decide +kernel
private theorem code_spec_62 : vectorCode (packed 610) + 4096 * vectorCode (packed 3601) = 14750306 := by decide +kernel
private theorem code_spec_63 : vectorCode (packed 3374) + 4096 * vectorCode (packed 3055) = 12516654 := by decide +kernel
private theorem code_spec_64 : vectorCode (packed 1230) + 4096 * vectorCode (packed 2878) = 11789518 := by decide +kernel
private theorem code_spec_65 : vectorCode (packed 832) + 4096 * vectorCode (packed 4010) = 16425792 := by decide +kernel
private theorem code_spec_66 : vectorCode (packed 3757) + 4096 * vectorCode (packed 1378) = 5648045 := by decide +kernel
private theorem code_spec_67 : vectorCode (packed 1230) + 4096 * vectorCode (packed 2437) = 9983182 := by decide +kernel
private theorem code_spec_68 : vectorCode (packed 592) + 4096 * vectorCode (packed 1032) = 4227664 := by decide +kernel
private theorem code_spec_69 : vectorCode (packed 3018) + 4096 * vectorCode (packed 3923) = 16071626 := by decide +kernel
private theorem code_spec_70 : vectorCode (packed 2746) + 4096 * vectorCode (packed 295) = 1211066 := by decide +kernel
private theorem code_spec_71 : vectorCode (packed 2361) + 4096 * vectorCode (packed 4010) = 16427321 := by decide +kernel
private theorem code_spec_72 : vectorCode (packed 507) + 4096 * vectorCode (packed 1354) = 5546491 := by decide +kernel
private theorem code_spec_73 : vectorCode (packed 3221) + 4096 * vectorCode (packed 1459) = 5979285 := by decide +kernel
private theorem code_spec_74 : vectorCode (packed 3612) + 4096 * vectorCode (packed 3015) = 12353052 := by decide +kernel
private theorem code_spec_75 : vectorCode (packed 3876) + 4096 * vectorCode (packed 3435) = 14073636 := by decide +kernel
private theorem code_spec_76 : vectorCode (packed 3140) + 4096 * vectorCode (packed 101) = 416836 := by decide +kernel
private theorem code_spec_77 : vectorCode (packed 3799) + 4096 * vectorCode (packed 1354) = 5549783 := by decide +kernel
private theorem code_spec_78 : vectorCode (packed 139) + 4096 * vectorCode (packed 551) = 2257035 := by decide +kernel
private theorem code_spec_79 : vectorCode (packed 3134) + 4096 * vectorCode (packed 3776) = 15469630 := by decide +kernel
private theorem code_spec_80 : vectorCode (packed 1998) + 4096 * vectorCode (packed 1032) = 4229070 := by decide +kernel
private theorem code_spec_81 : vectorCode (packed 3686) + 4096 * vectorCode (packed 3776) = 15470182 := by decide +kernel
private theorem code_spec_82 : vectorCode (packed 1204) + 4096 * vectorCode (packed 156) = 640180 := by decide +kernel
private theorem code_spec_83 : vectorCode (packed 4039) + 4096 * vectorCode (packed 101) = 417735 := by decide +kernel
private theorem code_spec_84 : vectorCode (packed 3166) + 4096 * vectorCode (packed 156) = 642142 := by decide +kernel
private theorem code_spec_85 : vectorCode (packed 938) + 4096 * vectorCode (packed 2786) = 11412394 := by decide +kernel
private theorem code_spec_86 : vectorCode (packed 3599) + 4096 * vectorCode (packed 214) = 880143 := by decide +kernel
private theorem code_spec_87 : vectorCode (packed 2188) + 4096 * vectorCode (packed 2) = 10380 := by decide +kernel
private theorem code_spec_88 : vectorCode (packed 3144) + 4096 * vectorCode (packed 4045) = 16571464 := by decide +kernel
private theorem code_spec_89 : vectorCode (packed 3122) + 4096 * vectorCode (packed 2) = 11314 := by decide +kernel
private theorem code_spec_90 : vectorCode (packed 3440) + 4096 * vectorCode (packed 1618) = 6630768 := by decide +kernel
private theorem code_spec_91 : vectorCode (packed 1943) + 4096 * vectorCode (packed 4045) = 16570263 := by decide +kernel
private theorem code_spec_92 : vectorCode (packed 3421) + 4096 * vectorCode (packed 3675) = 15056221 := by decide +kernel
private theorem code_spec_93 : vectorCode (packed 3144) + 4096 * vectorCode (packed 279) = 1145928 := by decide +kernel
private theorem code_spec_94 : vectorCode (packed 2029) + 4096 * vectorCode (packed 3675) = 15054829 := by decide +kernel
private theorem code_spec_95 : vectorCode (packed 2457) + 4096 * vectorCode (packed 320) = 1313177 := by decide +kernel
private theorem code_spec_96 : vectorCode (packed 2188) + 4096 * vectorCode (packed 2932) = 12011660 := by decide +kernel
private theorem code_spec_97 : vectorCode (packed 3830) + 4096 * vectorCode (packed 320) = 1314550 := by decide +kernel
private theorem code_spec_98 : vectorCode (packed 3599) + 4096 * vectorCode (packed 3727) = 15269391 := by decide +kernel
private theorem code_spec_99 : vectorCode (packed 658) + 4096 * vectorCode (packed 2271) = 9302674 := by decide +kernel
private theorem code_spec_100 : vectorCode (packed 1321) + 4096 * vectorCode (packed 320) = 1312041 := by decide +kernel
private theorem code_spec_101 : vectorCode (packed 1218) + 4096 * vectorCode (packed 214) = 877762 := by decide +kernel
private theorem code_spec_102 : vectorCode (packed 3830) + 4096 * vectorCode (packed 3994) = 16363254 := by decide +kernel
private theorem code_spec_103 : vectorCode (packed 3698) + 4096 * vectorCode (packed 214) = 880242 := by decide +kernel
private theorem code_spec_104 : vectorCode (packed 133) + 4096 * vectorCode (packed 4045) = 16568453 := by decide +kernel
private theorem code_spec_105 : vectorCode (packed 275) + 4096 * vectorCode (packed 1529) = 6263059 := by decide +kernel
private theorem code_spec_106 : vectorCode (packed 44) + 4096 * vectorCode (packed 3568) = 14614572 := by decide +kernel
private theorem code_spec_107 : vectorCode (packed 361) + 4096 * vectorCode (packed 1135) = 4649321 := by decide +kernel
private theorem code_spec_108 : vectorCode (packed 2029) + 4096 * vectorCode (packed 1325) = 5429229 := by decide +kernel
private theorem code_spec_109 : vectorCode (packed 4046) + 4096 * vectorCode (packed 893) = 3661774 := by decide +kernel
private theorem code_spec_110 : vectorCode (packed 86) + 4096 * vectorCode (packed 700) = 2867286 := by decide +kernel
private theorem code_spec_111 : vectorCode (packed 1406) + 4096 * vectorCode (packed 1618) = 6628734 := by decide +kernel
private theorem code_spec_112 : vectorCode (packed 1170) + 4096 * vectorCode (packed 3568) = 14615698 := by decide +kernel
private theorem code_spec_113 : vectorCode (packed 3492) + 4096 * vectorCode (packed 279) = 1146276 := by decide +kernel
private theorem code_spec_114 : vectorCode (packed 3360) + 4096 * vectorCode (packed 3675) = 15056160 := by decide +kernel
private theorem code_spec_115 : vectorCode (packed 276) + 4096 * vectorCode (packed 2741) = 11227412 := by decide +kernel
private theorem code_spec_116 : vectorCode (packed 44) + 4096 * vectorCode (packed 3702) = 15163436 := by decide +kernel
private theorem code_spec_117 : vectorCode (packed 361) + 4096 * vectorCode (packed 1080) = 4424041 := by decide +kernel
private theorem code_spec_118 : vectorCode (packed 3943) + 4096 * vectorCode (packed 279) = 1146727 := by decide +kernel
private theorem code_spec_119 : vectorCode (packed 3698) + 4096 * vectorCode (packed 2976) = 12193394 := by decide +kernel
private theorem code_spec_120 : vectorCode (packed 3943) + 4096 * vectorCode (packed 2786) = 11415399 := by decide +kernel
private theorem code_spec_121 : vectorCode (packed 1984) + 4096 * vectorCode (packed 893) = 3659712 := by decide +kernel
private theorem code_spec_122 : vectorCode (packed 1208) + 4096 * vectorCode (packed 2786) = 11412664 := by decide +kernel
private theorem code_spec_123 : vectorCode (packed 2531) + 4096 * vectorCode (packed 2932) = 12012003 := by decide +kernel
private theorem code_spec_124 : vectorCode (packed 133) + 4096 * vectorCode (packed 1080) = 4423813 := by decide +kernel
private theorem code_spec_125 : vectorCode (packed 851) + 4096 * vectorCode (packed 2932) = 12010323 := by decide +kernel
private theorem code_spec_126 : vectorCode (packed 1218) + 4096 * vectorCode (packed 1325) = 5428418 := by decide +kernel
private theorem code_spec_127 : vectorCode (packed 2268) + 4096 * vectorCode (packed 893) = 3659996 := by decide +kernel
private theorem code_spec_128 : vectorCode (packed 2532) + 4096 * vectorCode (packed 1080) = 4426212 := by decide +kernel

theorem pairCodes_spec : ∀ i, vectorCode (pairVectors i).1 + 4096 * vectorCode (pairVectors i).2 = pairCodes i := by
  intro i
  fin_cases i
  · exact code_spec_0
  · exact code_spec_1
  · exact code_spec_2
  · exact code_spec_3
  · exact code_spec_4
  · exact code_spec_5
  · exact code_spec_6
  · exact code_spec_7
  · exact code_spec_8
  · exact code_spec_9
  · exact code_spec_10
  · exact code_spec_11
  · exact code_spec_12
  · exact code_spec_13
  · exact code_spec_14
  · exact code_spec_15
  · exact code_spec_16
  · exact code_spec_17
  · exact code_spec_18
  · exact code_spec_19
  · exact code_spec_20
  · exact code_spec_21
  · exact code_spec_22
  · exact code_spec_23
  · exact code_spec_24
  · exact code_spec_25
  · exact code_spec_26
  · exact code_spec_27
  · exact code_spec_28
  · exact code_spec_29
  · exact code_spec_30
  · exact code_spec_31
  · exact code_spec_32
  · exact code_spec_33
  · exact code_spec_34
  · exact code_spec_35
  · exact code_spec_36
  · exact code_spec_37
  · exact code_spec_38
  · exact code_spec_39
  · exact code_spec_40
  · exact code_spec_41
  · exact code_spec_42
  · exact code_spec_43
  · exact code_spec_44
  · exact code_spec_45
  · exact code_spec_46
  · exact code_spec_47
  · exact code_spec_48
  · exact code_spec_49
  · exact code_spec_50
  · exact code_spec_51
  · exact code_spec_52
  · exact code_spec_53
  · exact code_spec_54
  · exact code_spec_55
  · exact code_spec_56
  · exact code_spec_57
  · exact code_spec_58
  · exact code_spec_59
  · exact code_spec_60
  · exact code_spec_61
  · exact code_spec_62
  · exact code_spec_63
  · exact code_spec_64
  · exact code_spec_65
  · exact code_spec_66
  · exact code_spec_67
  · exact code_spec_68
  · exact code_spec_69
  · exact code_spec_70
  · exact code_spec_71
  · exact code_spec_72
  · exact code_spec_73
  · exact code_spec_74
  · exact code_spec_75
  · exact code_spec_76
  · exact code_spec_77
  · exact code_spec_78
  · exact code_spec_79
  · exact code_spec_80
  · exact code_spec_81
  · exact code_spec_82
  · exact code_spec_83
  · exact code_spec_84
  · exact code_spec_85
  · exact code_spec_86
  · exact code_spec_87
  · exact code_spec_88
  · exact code_spec_89
  · exact code_spec_90
  · exact code_spec_91
  · exact code_spec_92
  · exact code_spec_93
  · exact code_spec_94
  · exact code_spec_95
  · exact code_spec_96
  · exact code_spec_97
  · exact code_spec_98
  · exact code_spec_99
  · exact code_spec_100
  · exact code_spec_101
  · exact code_spec_102
  · exact code_spec_103
  · exact code_spec_104
  · exact code_spec_105
  · exact code_spec_106
  · exact code_spec_107
  · exact code_spec_108
  · exact code_spec_109
  · exact code_spec_110
  · exact code_spec_111
  · exact code_spec_112
  · exact code_spec_113
  · exact code_spec_114
  · exact code_spec_115
  · exact code_spec_116
  · exact code_spec_117
  · exact code_spec_118
  · exact code_spec_119
  · exact code_spec_120
  · exact code_spec_121
  · exact code_spec_122
  · exact code_spec_123
  · exact code_spec_124
  · exact code_spec_125
  · exact code_spec_126
  · exact code_spec_127
  · exact code_spec_128

theorem pairVectors_injective : Function.Injective pairVectors := by
  intro i j h
  apply pairCodes_injective
  have hh := congrArg (fun v : BinarySpace × BinarySpace => vectorCode v.1 + 4096 * vectorCode v.2) h
  simpa only [pairCodes_spec] using hh

theorem pairParent_lt : ∀ i, (pairParent i).val < i.succ.val := by decide +kernel


end SylowCertificates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
