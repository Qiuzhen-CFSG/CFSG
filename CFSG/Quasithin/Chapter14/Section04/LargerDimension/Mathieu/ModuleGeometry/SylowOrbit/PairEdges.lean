module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit.PairCodes
/-!
# Native Mathieu Sylow certificates

Kernel-checked edges in the native ordered-pair orbit. Each edge is checked as two explicit matrix-vector products before the finite table is assembled.

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


private theorem step_0 : generatorMatrix 0 *ᵥ packed 1 = packed 3789 ∧ generatorMatrix 0 *ᵥ packed 2 = packed 3242 := by decide +kernel
private theorem step_1 : generatorMatrix 1 *ᵥ packed 1 = packed 2802 ∧ generatorMatrix 1 *ᵥ packed 2 = packed 551 := by decide +kernel
private theorem step_2 : generatorMatrix 2 *ᵥ packed 1 = packed 58 ∧ generatorMatrix 2 *ᵥ packed 2 = packed 2437 := by decide +kernel
private theorem step_3 : generatorMatrix 3 *ᵥ packed 1 = packed 632 ∧ generatorMatrix 3 *ᵥ packed 2 = packed 1378 := by decide +kernel
private theorem step_4 : generatorMatrix 4 *ᵥ packed 1 = packed 2802 ∧ generatorMatrix 4 *ᵥ packed 2 = packed 1459 := by decide +kernel
private theorem step_5 : generatorMatrix 5 *ᵥ packed 1 = packed 1575 ∧ generatorMatrix 5 *ᵥ packed 2 = packed 1800 := by decide +kernel
private theorem step_6 : generatorMatrix 1 *ᵥ packed 3789 = packed 366 ∧ generatorMatrix 1 *ᵥ packed 3242 = packed 2976 := by decide +kernel
private theorem step_7 : generatorMatrix 2 *ᵥ packed 3789 = packed 851 ∧ generatorMatrix 2 *ᵥ packed 3242 = packed 1325 := by decide +kernel
private theorem step_8 : generatorMatrix 3 *ᵥ packed 3789 = packed 276 ∧ generatorMatrix 3 *ᵥ packed 3242 = packed 1135 := by decide +kernel
private theorem step_9 : generatorMatrix 4 *ᵥ packed 3789 = packed 3122 ∧ generatorMatrix 4 *ᵥ packed 3242 = packed 3675 := by decide +kernel
private theorem step_10 : generatorMatrix 5 *ᵥ packed 3789 = packed 275 ∧ generatorMatrix 5 *ᵥ packed 3242 = packed 3727 := by decide +kernel
private theorem step_11 : generatorMatrix 2 *ᵥ packed 2802 = packed 2462 ∧ generatorMatrix 2 *ᵥ packed 551 = packed 3727 := by decide +kernel
private theorem step_12 : generatorMatrix 3 *ᵥ packed 2802 = packed 248 ∧ generatorMatrix 3 *ᵥ packed 551 = packed 4045 := by decide +kernel
private theorem step_13 : generatorMatrix 4 *ᵥ packed 2802 = packed 1 ∧ generatorMatrix 4 *ᵥ packed 551 = packed 1529 := by decide +kernel
private theorem step_14 : generatorMatrix 5 *ᵥ packed 2802 = packed 3038 ∧ generatorMatrix 5 *ᵥ packed 551 = packed 1325 := by decide +kernel
private theorem step_15 : generatorMatrix 3 *ᵥ packed 58 = packed 2532 ∧ generatorMatrix 3 *ᵥ packed 2437 = packed 320 := by decide +kernel
private theorem step_16 : generatorMatrix 4 *ᵥ packed 58 = packed 2462 ∧ generatorMatrix 4 *ᵥ packed 2437 = packed 2932 := by decide +kernel
private theorem step_17 : generatorMatrix 5 *ᵥ packed 58 = packed 2531 ∧ generatorMatrix 5 *ᵥ packed 2437 = packed 2976 := by decide +kernel
private theorem step_18 : generatorMatrix 1 *ᵥ packed 632 = packed 3492 ∧ generatorMatrix 1 *ᵥ packed 1378 = packed 1135 := by decide +kernel
private theorem step_19 : generatorMatrix 3 *ᵥ packed 632 = packed 3421 ∧ generatorMatrix 3 *ᵥ packed 1378 = packed 2976 := by decide +kernel
private theorem step_20 : generatorMatrix 4 *ᵥ packed 632 = packed 3228 ∧ generatorMatrix 4 *ᵥ packed 1378 = packed 3568 := by decide +kernel
private theorem step_21 : generatorMatrix 5 *ᵥ packed 632 = packed 1659 ∧ generatorMatrix 5 *ᵥ packed 1378 = packed 1135 := by decide +kernel
private theorem step_22 : generatorMatrix 0 *ᵥ packed 2802 = packed 366 ∧ generatorMatrix 0 *ᵥ packed 1459 = packed 1529 := by decide +kernel
private theorem step_23 : generatorMatrix 3 *ᵥ packed 2802 = packed 248 ∧ generatorMatrix 3 *ᵥ packed 1459 = packed 2741 := by decide +kernel
private theorem step_24 : generatorMatrix 5 *ᵥ packed 2802 = packed 3038 ∧ generatorMatrix 5 *ᵥ packed 1459 = packed 1529 := by decide +kernel
private theorem step_25 : generatorMatrix 3 *ᵥ packed 1575 = packed 983 ∧ generatorMatrix 3 *ᵥ packed 1800 = packed 2786 := by decide +kernel
private theorem step_26 : generatorMatrix 4 *ᵥ packed 1575 = packed 3869 ∧ generatorMatrix 4 *ᵥ packed 1800 = packed 214 := by decide +kernel
private theorem step_27 : generatorMatrix 2 *ᵥ packed 366 = packed 2696 ∧ generatorMatrix 2 *ᵥ packed 2976 = packed 1800 := by decide +kernel
private theorem step_28 : generatorMatrix 3 *ᵥ packed 366 = packed 507 ∧ generatorMatrix 3 *ᵥ packed 2976 = packed 3055 := by decide +kernel
private theorem step_29 : generatorMatrix 4 *ᵥ packed 366 = packed 681 ∧ generatorMatrix 4 *ᵥ packed 2976 = packed 2878 := by decide +kernel
private theorem step_30 : generatorMatrix 5 *ᵥ packed 366 = packed 3221 ∧ generatorMatrix 5 *ᵥ packed 2976 = packed 2437 := by decide +kernel
private theorem step_31 : generatorMatrix 3 *ᵥ packed 851 = packed 514 ∧ generatorMatrix 3 *ᵥ packed 1325 = packed 77 := by decide +kernel
private theorem step_32 : generatorMatrix 4 *ᵥ packed 851 = packed 1772 ∧ generatorMatrix 4 *ᵥ packed 1325 = packed 156 := by decide +kernel
private theorem step_33 : generatorMatrix 5 *ᵥ packed 851 = packed 1629 ∧ generatorMatrix 5 *ᵥ packed 1325 = packed 551 := by decide +kernel
private theorem step_34 : generatorMatrix 1 *ᵥ packed 276 = packed 3487 ∧ generatorMatrix 1 *ᵥ packed 1135 = packed 1378 := by decide +kernel
private theorem step_35 : generatorMatrix 3 *ᵥ packed 276 = packed 681 ∧ generatorMatrix 3 *ᵥ packed 1135 = packed 551 := by decide +kernel
private theorem step_36 : generatorMatrix 4 *ᵥ packed 276 = packed 3239 ∧ generatorMatrix 4 *ᵥ packed 1135 = packed 4010 := by decide +kernel
private theorem step_37 : generatorMatrix 5 *ᵥ packed 276 = packed 4039 ∧ generatorMatrix 5 *ᵥ packed 1135 = packed 1378 := by decide +kernel
private theorem step_38 : generatorMatrix 0 *ᵥ packed 3122 = packed 1686 ∧ generatorMatrix 0 *ᵥ packed 3675 = packed 2878 := by decide +kernel
private theorem step_39 : generatorMatrix 3 *ᵥ packed 3122 = packed 3487 ∧ generatorMatrix 3 *ᵥ packed 3675 = packed 3015 := by decide +kernel
private theorem step_40 : generatorMatrix 5 *ᵥ packed 3122 = packed 3708 ∧ generatorMatrix 5 *ᵥ packed 3675 = packed 2878 := by decide +kernel
private theorem step_41 : generatorMatrix 3 *ᵥ packed 275 = packed 985 ∧ generatorMatrix 3 *ᵥ packed 3727 = packed 3776 := by decide +kernel
private theorem step_42 : generatorMatrix 4 *ᵥ packed 275 = packed 1629 ∧ generatorMatrix 4 *ᵥ packed 3727 = packed 3601 := by decide +kernel
private theorem step_43 : generatorMatrix 3 *ᵥ packed 2462 = packed 3852 ∧ generatorMatrix 3 *ᵥ packed 3727 = packed 3776 := by decide +kernel
private theorem step_44 : generatorMatrix 4 *ᵥ packed 2462 = packed 58 ∧ generatorMatrix 4 *ᵥ packed 3727 = packed 3601 := by decide +kernel
private theorem step_45 : generatorMatrix 5 *ᵥ packed 2462 = packed 610 ∧ generatorMatrix 5 *ᵥ packed 3727 = packed 3242 := by decide +kernel
private theorem step_46 : generatorMatrix 1 *ᵥ packed 248 = packed 3612 ∧ generatorMatrix 1 *ᵥ packed 4045 = packed 3055 := by decide +kernel
private theorem step_47 : generatorMatrix 3 *ᵥ packed 248 = packed 1686 ∧ generatorMatrix 3 *ᵥ packed 4045 = packed 3242 := by decide +kernel
private theorem step_48 : generatorMatrix 4 *ᵥ packed 248 = packed 3876 ∧ generatorMatrix 4 *ᵥ packed 4045 = packed 295 := by decide +kernel
private theorem step_49 : generatorMatrix 5 *ᵥ packed 248 = packed 3140 ∧ generatorMatrix 5 *ᵥ packed 4045 = packed 3055 := by decide +kernel
private theorem step_50 : generatorMatrix 0 *ᵥ packed 1 = packed 3789 ∧ generatorMatrix 0 *ᵥ packed 1529 = packed 1459 := by decide +kernel
private theorem step_51 : generatorMatrix 3 *ᵥ packed 1 = packed 632 ∧ generatorMatrix 3 *ᵥ packed 1529 = packed 1354 := by decide +kernel
private theorem step_52 : generatorMatrix 5 *ᵥ packed 1 = packed 1575 ∧ generatorMatrix 5 *ᵥ packed 1529 = packed 1459 := by decide +kernel
private theorem step_53 : generatorMatrix 3 *ᵥ packed 3038 = packed 3799 ∧ generatorMatrix 3 *ᵥ packed 1325 = packed 77 := by decide +kernel
private theorem step_54 : generatorMatrix 4 *ᵥ packed 3038 = packed 139 ∧ generatorMatrix 4 *ᵥ packed 1325 = packed 156 := by decide +kernel
private theorem step_55 : generatorMatrix 1 *ᵥ packed 2532 = packed 872 ∧ generatorMatrix 1 *ᵥ packed 320 = packed 77 := by decide +kernel
private theorem step_56 : generatorMatrix 3 *ᵥ packed 2532 = packed 3166 ∧ generatorMatrix 3 *ᵥ packed 320 = packed 1800 := by decide +kernel
private theorem step_57 : generatorMatrix 4 *ᵥ packed 2532 = packed 3636 ∧ generatorMatrix 4 *ᵥ packed 320 = packed 2693 := by decide +kernel
private theorem step_58 : generatorMatrix 5 *ᵥ packed 2532 = packed 304 ∧ generatorMatrix 5 *ᵥ packed 320 = packed 77 := by decide +kernel
private theorem step_59 : generatorMatrix 0 *ᵥ packed 2462 = packed 2696 ∧ generatorMatrix 0 *ᵥ packed 2932 = packed 3601 := by decide +kernel
private theorem step_60 : generatorMatrix 3 *ᵥ packed 2462 = packed 3852 ∧ generatorMatrix 3 *ᵥ packed 2932 = packed 3816 := by decide +kernel
private theorem step_61 : generatorMatrix 5 *ᵥ packed 2462 = packed 610 ∧ generatorMatrix 5 *ᵥ packed 2932 = packed 3601 := by decide +kernel
private theorem step_62 : generatorMatrix 3 *ᵥ packed 2531 = packed 3374 ∧ generatorMatrix 3 *ᵥ packed 2976 = packed 3055 := by decide +kernel
private theorem step_63 : generatorMatrix 4 *ᵥ packed 2531 = packed 1230 ∧ generatorMatrix 4 *ᵥ packed 2976 = packed 2878 := by decide +kernel
private theorem step_64 : generatorMatrix 4 *ᵥ packed 3492 = packed 832 ∧ generatorMatrix 4 *ᵥ packed 1135 = packed 4010 := by decide +kernel
private theorem step_65 : generatorMatrix 5 *ᵥ packed 3492 = packed 3757 ∧ generatorMatrix 5 *ᵥ packed 1135 = packed 1378 := by decide +kernel
private theorem step_66 : generatorMatrix 5 *ᵥ packed 3421 = packed 1230 ∧ generatorMatrix 5 *ᵥ packed 2976 = packed 2437 := by decide +kernel
private theorem step_67 : generatorMatrix 0 *ᵥ packed 3228 = packed 592 ∧ generatorMatrix 0 *ᵥ packed 3568 = packed 1032 := by decide +kernel
private theorem step_68 : generatorMatrix 3 *ᵥ packed 3228 = packed 3018 ∧ generatorMatrix 3 *ᵥ packed 3568 = packed 3923 := by decide +kernel
private theorem step_69 : generatorMatrix 5 *ᵥ packed 3228 = packed 2746 ∧ generatorMatrix 5 *ᵥ packed 3568 = packed 295 := by decide +kernel
private theorem step_70 : generatorMatrix 4 *ᵥ packed 1659 = packed 2361 ∧ generatorMatrix 4 *ᵥ packed 1135 = packed 4010 := by decide +kernel
private theorem step_71 : generatorMatrix 3 *ᵥ packed 366 = packed 507 ∧ generatorMatrix 3 *ᵥ packed 1529 = packed 1354 := by decide +kernel
private theorem step_72 : generatorMatrix 5 *ᵥ packed 366 = packed 3221 ∧ generatorMatrix 5 *ᵥ packed 1529 = packed 1459 := by decide +kernel
private theorem step_73 : generatorMatrix 1 *ᵥ packed 248 = packed 3612 ∧ generatorMatrix 1 *ᵥ packed 2741 = packed 3015 := by decide +kernel
private theorem step_74 : generatorMatrix 4 *ᵥ packed 248 = packed 3876 ∧ generatorMatrix 4 *ᵥ packed 2741 = packed 3435 := by decide +kernel
private theorem step_75 : generatorMatrix 5 *ᵥ packed 248 = packed 3140 ∧ generatorMatrix 5 *ᵥ packed 2741 = packed 101 := by decide +kernel
private theorem step_76 : generatorMatrix 3 *ᵥ packed 3038 = packed 3799 ∧ generatorMatrix 3 *ᵥ packed 1529 = packed 1354 := by decide +kernel
private theorem step_77 : generatorMatrix 4 *ᵥ packed 3038 = packed 139 ∧ generatorMatrix 4 *ᵥ packed 1529 = packed 551 := by decide +kernel
private theorem step_78 : generatorMatrix 1 *ᵥ packed 983 = packed 3134 ∧ generatorMatrix 1 *ᵥ packed 2786 = packed 3776 := by decide +kernel
private theorem step_79 : generatorMatrix 4 *ᵥ packed 983 = packed 1998 ∧ generatorMatrix 4 *ᵥ packed 2786 = packed 1032 := by decide +kernel
private theorem step_80 : generatorMatrix 5 *ᵥ packed 983 = packed 3686 ∧ generatorMatrix 5 *ᵥ packed 2786 = packed 3776 := by decide +kernel
private theorem step_81 : generatorMatrix 0 *ᵥ packed 3869 = packed 1204 ∧ generatorMatrix 0 *ᵥ packed 214 = packed 156 := by decide +kernel
private theorem step_82 : generatorMatrix 3 *ᵥ packed 3869 = packed 4039 ∧ generatorMatrix 3 *ᵥ packed 214 = packed 101 := by decide +kernel
private theorem step_83 : generatorMatrix 5 *ᵥ packed 3869 = packed 3166 ∧ generatorMatrix 5 *ᵥ packed 214 = packed 156 := by decide +kernel
private theorem step_84 : generatorMatrix 3 *ᵥ packed 2696 = packed 938 ∧ generatorMatrix 3 *ᵥ packed 1800 = packed 2786 := by decide +kernel
private theorem step_85 : generatorMatrix 4 *ᵥ packed 2696 = packed 3599 ∧ generatorMatrix 4 *ᵥ packed 1800 = packed 214 := by decide +kernel
private theorem step_86 : generatorMatrix 5 *ᵥ packed 2696 = packed 2188 ∧ generatorMatrix 5 *ᵥ packed 1800 = packed 2 := by decide +kernel
private theorem step_87 : generatorMatrix 1 *ᵥ packed 507 = packed 3144 ∧ generatorMatrix 1 *ᵥ packed 3055 = packed 4045 := by decide +kernel
private theorem step_88 : generatorMatrix 3 *ᵥ packed 507 = packed 3122 ∧ generatorMatrix 3 *ᵥ packed 3055 = packed 2 := by decide +kernel
private theorem step_89 : generatorMatrix 4 *ᵥ packed 507 = packed 3440 ∧ generatorMatrix 4 *ᵥ packed 3055 = packed 1618 := by decide +kernel
private theorem step_90 : generatorMatrix 5 *ᵥ packed 507 = packed 1943 ∧ generatorMatrix 5 *ᵥ packed 3055 = packed 4045 := by decide +kernel
private theorem step_91 : generatorMatrix 0 *ᵥ packed 681 = packed 3421 ∧ generatorMatrix 0 *ᵥ packed 2878 = packed 3675 := by decide +kernel
private theorem step_92 : generatorMatrix 3 *ᵥ packed 681 = packed 3144 ∧ generatorMatrix 3 *ᵥ packed 2878 = packed 279 := by decide +kernel
private theorem step_93 : generatorMatrix 5 *ᵥ packed 681 = packed 2029 ∧ generatorMatrix 5 *ᵥ packed 2878 = packed 3675 := by decide +kernel
private theorem step_94 : generatorMatrix 3 *ᵥ packed 3221 = packed 2457 ∧ generatorMatrix 3 *ᵥ packed 2437 = packed 320 := by decide +kernel
private theorem step_95 : generatorMatrix 4 *ᵥ packed 3221 = packed 2188 ∧ generatorMatrix 4 *ᵥ packed 2437 = packed 2932 := by decide +kernel
private theorem step_96 : generatorMatrix 1 *ᵥ packed 514 = packed 3830 ∧ generatorMatrix 1 *ᵥ packed 77 = packed 320 := by decide +kernel
private theorem step_97 : generatorMatrix 3 *ᵥ packed 514 = packed 3599 ∧ generatorMatrix 3 *ᵥ packed 77 = packed 3727 := by decide +kernel
private theorem step_98 : generatorMatrix 4 *ᵥ packed 514 = packed 658 ∧ generatorMatrix 4 *ᵥ packed 77 = packed 2271 := by decide +kernel
private theorem step_99 : generatorMatrix 5 *ᵥ packed 514 = packed 1321 ∧ generatorMatrix 5 *ᵥ packed 77 = packed 320 := by decide +kernel
private theorem step_100 : generatorMatrix 0 *ᵥ packed 1772 = packed 1218 ∧ generatorMatrix 0 *ᵥ packed 156 = packed 214 := by decide +kernel
private theorem step_101 : generatorMatrix 3 *ᵥ packed 1772 = packed 3830 ∧ generatorMatrix 3 *ᵥ packed 156 = packed 3994 := by decide +kernel
private theorem step_102 : generatorMatrix 5 *ᵥ packed 1772 = packed 3698 ∧ generatorMatrix 5 *ᵥ packed 156 = packed 214 := by decide +kernel
private theorem step_103 : generatorMatrix 3 *ᵥ packed 1629 = packed 133 ∧ generatorMatrix 3 *ᵥ packed 551 = packed 4045 := by decide +kernel
private theorem step_104 : generatorMatrix 4 *ᵥ packed 1629 = packed 275 ∧ generatorMatrix 4 *ᵥ packed 551 = packed 1529 := by decide +kernel
private theorem step_105 : generatorMatrix 4 *ᵥ packed 3487 = packed 44 ∧ generatorMatrix 4 *ᵥ packed 1378 = packed 3568 := by decide +kernel
private theorem step_106 : generatorMatrix 5 *ᵥ packed 3487 = packed 361 ∧ generatorMatrix 5 *ᵥ packed 1378 = packed 1135 := by decide +kernel
private theorem step_107 : generatorMatrix 5 *ᵥ packed 681 = packed 2029 ∧ generatorMatrix 5 *ᵥ packed 551 = packed 1325 := by decide +kernel
private theorem step_108 : generatorMatrix 0 *ᵥ packed 3239 = packed 4046 ∧ generatorMatrix 0 *ᵥ packed 4010 = packed 893 := by decide +kernel
private theorem step_109 : generatorMatrix 3 *ᵥ packed 3239 = packed 86 ∧ generatorMatrix 3 *ᵥ packed 4010 = packed 700 := by decide +kernel
private theorem step_110 : generatorMatrix 5 *ᵥ packed 3239 = packed 1406 ∧ generatorMatrix 5 *ᵥ packed 4010 = packed 1618 := by decide +kernel
private theorem step_111 : generatorMatrix 4 *ᵥ packed 4039 = packed 1170 ∧ generatorMatrix 4 *ᵥ packed 1378 = packed 3568 := by decide +kernel
private theorem step_112 : generatorMatrix 3 *ᵥ packed 1686 = packed 3492 ∧ generatorMatrix 3 *ᵥ packed 2878 = packed 279 := by decide +kernel
private theorem step_113 : generatorMatrix 5 *ᵥ packed 1686 = packed 3360 ∧ generatorMatrix 5 *ᵥ packed 2878 = packed 3675 := by decide +kernel
private theorem step_114 : generatorMatrix 1 *ᵥ packed 3487 = packed 276 ∧ generatorMatrix 1 *ᵥ packed 3015 = packed 2741 := by decide +kernel
private theorem step_115 : generatorMatrix 4 *ᵥ packed 3487 = packed 44 ∧ generatorMatrix 4 *ᵥ packed 3015 = packed 3702 := by decide +kernel
private theorem step_116 : generatorMatrix 5 *ᵥ packed 3487 = packed 361 ∧ generatorMatrix 5 *ᵥ packed 3015 = packed 1080 := by decide +kernel
private theorem step_117 : generatorMatrix 3 *ᵥ packed 3708 = packed 3943 ∧ generatorMatrix 3 *ᵥ packed 2878 = packed 279 := by decide +kernel
private theorem step_118 : generatorMatrix 4 *ᵥ packed 3708 = packed 3698 ∧ generatorMatrix 4 *ᵥ packed 2878 = packed 2976 := by decide +kernel
private theorem step_119 : generatorMatrix 1 *ᵥ packed 985 = packed 3943 ∧ generatorMatrix 1 *ᵥ packed 3776 = packed 2786 := by decide +kernel
private theorem step_120 : generatorMatrix 4 *ᵥ packed 985 = packed 1984 ∧ generatorMatrix 4 *ᵥ packed 3776 = packed 893 := by decide +kernel
private theorem step_121 : generatorMatrix 5 *ᵥ packed 985 = packed 1208 ∧ generatorMatrix 5 *ᵥ packed 3776 = packed 2786 := by decide +kernel
private theorem step_122 : generatorMatrix 0 *ᵥ packed 1629 = packed 2531 ∧ generatorMatrix 0 *ᵥ packed 3601 = packed 2932 := by decide +kernel
private theorem step_123 : generatorMatrix 3 *ᵥ packed 1629 = packed 133 ∧ generatorMatrix 3 *ᵥ packed 3601 = packed 1080 := by decide +kernel
private theorem step_124 : generatorMatrix 5 *ᵥ packed 1629 = packed 851 ∧ generatorMatrix 5 *ᵥ packed 3601 = packed 2932 := by decide +kernel
private theorem step_125 : generatorMatrix 3 *ᵥ packed 3852 = packed 1218 ∧ generatorMatrix 3 *ᵥ packed 3776 = packed 1325 := by decide +kernel
private theorem step_126 : generatorMatrix 4 *ᵥ packed 3852 = packed 2268 ∧ generatorMatrix 4 *ᵥ packed 3776 = packed 893 := by decide +kernel
private theorem step_127 : generatorMatrix 3 *ᵥ packed 58 = packed 2532 ∧ generatorMatrix 3 *ᵥ packed 3601 = packed 1080 := by decide +kernel

theorem pair_steps : ∀ i,
    generatorMatrix (pairActor i) *ᵥ (pairVectors (pairParent i)).1 = (pairVectors i.succ).1 ∧
    generatorMatrix (pairActor i) *ᵥ (pairVectors (pairParent i)).2 = (pairVectors i.succ).2 := by
  intro i
  fin_cases i
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3
  · exact step_4
  · exact step_5
  · exact step_6
  · exact step_7
  · exact step_8
  · exact step_9
  · exact step_10
  · exact step_11
  · exact step_12
  · exact step_13
  · exact step_14
  · exact step_15
  · exact step_16
  · exact step_17
  · exact step_18
  · exact step_19
  · exact step_20
  · exact step_21
  · exact step_22
  · exact step_23
  · exact step_24
  · exact step_25
  · exact step_26
  · exact step_27
  · exact step_28
  · exact step_29
  · exact step_30
  · exact step_31
  · exact step_32
  · exact step_33
  · exact step_34
  · exact step_35
  · exact step_36
  · exact step_37
  · exact step_38
  · exact step_39
  · exact step_40
  · exact step_41
  · exact step_42
  · exact step_43
  · exact step_44
  · exact step_45
  · exact step_46
  · exact step_47
  · exact step_48
  · exact step_49
  · exact step_50
  · exact step_51
  · exact step_52
  · exact step_53
  · exact step_54
  · exact step_55
  · exact step_56
  · exact step_57
  · exact step_58
  · exact step_59
  · exact step_60
  · exact step_61
  · exact step_62
  · exact step_63
  · exact step_64
  · exact step_65
  · exact step_66
  · exact step_67
  · exact step_68
  · exact step_69
  · exact step_70
  · exact step_71
  · exact step_72
  · exact step_73
  · exact step_74
  · exact step_75
  · exact step_76
  · exact step_77
  · exact step_78
  · exact step_79
  · exact step_80
  · exact step_81
  · exact step_82
  · exact step_83
  · exact step_84
  · exact step_85
  · exact step_86
  · exact step_87
  · exact step_88
  · exact step_89
  · exact step_90
  · exact step_91
  · exact step_92
  · exact step_93
  · exact step_94
  · exact step_95
  · exact step_96
  · exact step_97
  · exact step_98
  · exact step_99
  · exact step_100
  · exact step_101
  · exact step_102
  · exact step_103
  · exact step_104
  · exact step_105
  · exact step_106
  · exact step_107
  · exact step_108
  · exact step_109
  · exact step_110
  · exact step_111
  · exact step_112
  · exact step_113
  · exact step_114
  · exact step_115
  · exact step_116
  · exact step_117
  · exact step_118
  · exact step_119
  · exact step_120
  · exact step_121
  · exact step_122
  · exact step_123
  · exact step_124
  · exact step_125
  · exact step_126
  · exact step_127


end SylowCertificates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
