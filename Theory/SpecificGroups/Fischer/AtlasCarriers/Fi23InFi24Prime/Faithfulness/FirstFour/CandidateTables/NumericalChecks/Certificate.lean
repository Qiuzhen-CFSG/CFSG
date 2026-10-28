module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.NumericalChecks.Checker

/-!
# Kernel certificates for all full-ambient candidate stages

Each leaf proof checks 1024 consecutive indices by kernel reduction. Adjacent
leaves are joined without repeating their computations. The four intervals
cover all 306936 ambient letters and 264 harmless modular padding indices.
Every leaf checks all sixteen inverse/composition identities, including the
literal final conjugation for candidate B.

The strict checker was measured before scaling. Sequential declaration
elaboration bounds the live kernel-reduction memory to one leaf at a time.
Reproduce this proof source with `NumericalChecks/source/generate.py --check`.
Source: `WordSetup`, retained ATLAS F24G1-p306936B0 data, GLS3 Table 5.3v.
-/

set_option Elab.async false

namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.NumericalChecks
open Certificate

private theorem block_0_10 : checkPow stageTest 0 10 = true := by
  decide +kernel

private theorem block_1024_10 : checkPow stageTest 1024 10 = true := by
  decide +kernel

private theorem block_2048_10 : checkPow stageTest 2048 10 = true := by
  decide +kernel

private theorem block_3072_10 : checkPow stageTest 3072 10 = true := by
  decide +kernel

private theorem block_4096_10 : checkPow stageTest 4096 10 = true := by
  decide +kernel

private theorem block_5120_10 : checkPow stageTest 5120 10 = true := by
  decide +kernel

private theorem block_6144_10 : checkPow stageTest 6144 10 = true := by
  decide +kernel

private theorem block_7168_10 : checkPow stageTest 7168 10 = true := by
  decide +kernel

private theorem block_8192_10 : checkPow stageTest 8192 10 = true := by
  decide +kernel

private theorem block_9216_10 : checkPow stageTest 9216 10 = true := by
  decide +kernel

private theorem block_10240_10 : checkPow stageTest 10240 10 = true := by
  decide +kernel

private theorem block_11264_10 : checkPow stageTest 11264 10 = true := by
  decide +kernel

private theorem block_12288_10 : checkPow stageTest 12288 10 = true := by
  decide +kernel

private theorem block_13312_10 : checkPow stageTest 13312 10 = true := by
  decide +kernel

private theorem block_14336_10 : checkPow stageTest 14336 10 = true := by
  decide +kernel

private theorem block_15360_10 : checkPow stageTest 15360 10 = true := by
  decide +kernel

private theorem block_16384_10 : checkPow stageTest 16384 10 = true := by
  decide +kernel

private theorem block_17408_10 : checkPow stageTest 17408 10 = true := by
  decide +kernel

private theorem block_18432_10 : checkPow stageTest 18432 10 = true := by
  decide +kernel

private theorem block_19456_10 : checkPow stageTest 19456 10 = true := by
  decide +kernel

private theorem block_20480_10 : checkPow stageTest 20480 10 = true := by
  decide +kernel

private theorem block_21504_10 : checkPow stageTest 21504 10 = true := by
  decide +kernel

private theorem block_22528_10 : checkPow stageTest 22528 10 = true := by
  decide +kernel

private theorem block_23552_10 : checkPow stageTest 23552 10 = true := by
  decide +kernel

private theorem block_24576_10 : checkPow stageTest 24576 10 = true := by
  decide +kernel

private theorem block_25600_10 : checkPow stageTest 25600 10 = true := by
  decide +kernel

private theorem block_26624_10 : checkPow stageTest 26624 10 = true := by
  decide +kernel

private theorem block_27648_10 : checkPow stageTest 27648 10 = true := by
  decide +kernel

private theorem block_28672_10 : checkPow stageTest 28672 10 = true := by
  decide +kernel

private theorem block_29696_10 : checkPow stageTest 29696 10 = true := by
  decide +kernel

private theorem block_30720_10 : checkPow stageTest 30720 10 = true := by
  decide +kernel

private theorem block_31744_10 : checkPow stageTest 31744 10 = true := by
  decide +kernel

private theorem block_32768_10 : checkPow stageTest 32768 10 = true := by
  decide +kernel

private theorem block_33792_10 : checkPow stageTest 33792 10 = true := by
  decide +kernel

private theorem block_34816_10 : checkPow stageTest 34816 10 = true := by
  decide +kernel

private theorem block_35840_10 : checkPow stageTest 35840 10 = true := by
  decide +kernel

private theorem block_36864_10 : checkPow stageTest 36864 10 = true := by
  decide +kernel

private theorem block_37888_10 : checkPow stageTest 37888 10 = true := by
  decide +kernel

private theorem block_38912_10 : checkPow stageTest 38912 10 = true := by
  decide +kernel

private theorem block_39936_10 : checkPow stageTest 39936 10 = true := by
  decide +kernel

private theorem block_40960_10 : checkPow stageTest 40960 10 = true := by
  decide +kernel

private theorem block_41984_10 : checkPow stageTest 41984 10 = true := by
  decide +kernel

private theorem block_43008_10 : checkPow stageTest 43008 10 = true := by
  decide +kernel

private theorem block_44032_10 : checkPow stageTest 44032 10 = true := by
  decide +kernel

private theorem block_45056_10 : checkPow stageTest 45056 10 = true := by
  decide +kernel

private theorem block_46080_10 : checkPow stageTest 46080 10 = true := by
  decide +kernel

private theorem block_47104_10 : checkPow stageTest 47104 10 = true := by
  decide +kernel

private theorem block_48128_10 : checkPow stageTest 48128 10 = true := by
  decide +kernel

private theorem block_49152_10 : checkPow stageTest 49152 10 = true := by
  decide +kernel

private theorem block_50176_10 : checkPow stageTest 50176 10 = true := by
  decide +kernel

private theorem block_51200_10 : checkPow stageTest 51200 10 = true := by
  decide +kernel

private theorem block_52224_10 : checkPow stageTest 52224 10 = true := by
  decide +kernel

private theorem block_53248_10 : checkPow stageTest 53248 10 = true := by
  decide +kernel

private theorem block_54272_10 : checkPow stageTest 54272 10 = true := by
  decide +kernel

private theorem block_55296_10 : checkPow stageTest 55296 10 = true := by
  decide +kernel

private theorem block_56320_10 : checkPow stageTest 56320 10 = true := by
  decide +kernel

private theorem block_57344_10 : checkPow stageTest 57344 10 = true := by
  decide +kernel

private theorem block_58368_10 : checkPow stageTest 58368 10 = true := by
  decide +kernel

private theorem block_59392_10 : checkPow stageTest 59392 10 = true := by
  decide +kernel

private theorem block_60416_10 : checkPow stageTest 60416 10 = true := by
  decide +kernel

private theorem block_61440_10 : checkPow stageTest 61440 10 = true := by
  decide +kernel

private theorem block_62464_10 : checkPow stageTest 62464 10 = true := by
  decide +kernel

private theorem block_63488_10 : checkPow stageTest 63488 10 = true := by
  decide +kernel

private theorem block_64512_10 : checkPow stageTest 64512 10 = true := by
  decide +kernel

private theorem block_65536_10 : checkPow stageTest 65536 10 = true := by
  decide +kernel

private theorem block_66560_10 : checkPow stageTest 66560 10 = true := by
  decide +kernel

private theorem block_67584_10 : checkPow stageTest 67584 10 = true := by
  decide +kernel

private theorem block_68608_10 : checkPow stageTest 68608 10 = true := by
  decide +kernel

private theorem block_69632_10 : checkPow stageTest 69632 10 = true := by
  decide +kernel

private theorem block_70656_10 : checkPow stageTest 70656 10 = true := by
  decide +kernel

private theorem block_71680_10 : checkPow stageTest 71680 10 = true := by
  decide +kernel

private theorem block_72704_10 : checkPow stageTest 72704 10 = true := by
  decide +kernel

private theorem block_73728_10 : checkPow stageTest 73728 10 = true := by
  decide +kernel

private theorem block_74752_10 : checkPow stageTest 74752 10 = true := by
  decide +kernel

private theorem block_75776_10 : checkPow stageTest 75776 10 = true := by
  decide +kernel

private theorem block_76800_10 : checkPow stageTest 76800 10 = true := by
  decide +kernel

private theorem block_77824_10 : checkPow stageTest 77824 10 = true := by
  decide +kernel

private theorem block_78848_10 : checkPow stageTest 78848 10 = true := by
  decide +kernel

private theorem block_79872_10 : checkPow stageTest 79872 10 = true := by
  decide +kernel

private theorem block_80896_10 : checkPow stageTest 80896 10 = true := by
  decide +kernel

private theorem block_81920_10 : checkPow stageTest 81920 10 = true := by
  decide +kernel

private theorem block_82944_10 : checkPow stageTest 82944 10 = true := by
  decide +kernel

private theorem block_83968_10 : checkPow stageTest 83968 10 = true := by
  decide +kernel

private theorem block_84992_10 : checkPow stageTest 84992 10 = true := by
  decide +kernel

private theorem block_86016_10 : checkPow stageTest 86016 10 = true := by
  decide +kernel

private theorem block_87040_10 : checkPow stageTest 87040 10 = true := by
  decide +kernel

private theorem block_88064_10 : checkPow stageTest 88064 10 = true := by
  decide +kernel

private theorem block_89088_10 : checkPow stageTest 89088 10 = true := by
  decide +kernel

private theorem block_90112_10 : checkPow stageTest 90112 10 = true := by
  decide +kernel

private theorem block_91136_10 : checkPow stageTest 91136 10 = true := by
  decide +kernel

private theorem block_92160_10 : checkPow stageTest 92160 10 = true := by
  decide +kernel

private theorem block_93184_10 : checkPow stageTest 93184 10 = true := by
  decide +kernel

private theorem block_94208_10 : checkPow stageTest 94208 10 = true := by
  decide +kernel

private theorem block_95232_10 : checkPow stageTest 95232 10 = true := by
  decide +kernel

private theorem block_96256_10 : checkPow stageTest 96256 10 = true := by
  decide +kernel

private theorem block_97280_10 : checkPow stageTest 97280 10 = true := by
  decide +kernel

private theorem block_98304_10 : checkPow stageTest 98304 10 = true := by
  decide +kernel

private theorem block_99328_10 : checkPow stageTest 99328 10 = true := by
  decide +kernel

private theorem block_100352_10 : checkPow stageTest 100352 10 = true := by
  decide +kernel

private theorem block_101376_10 : checkPow stageTest 101376 10 = true := by
  decide +kernel

private theorem block_102400_10 : checkPow stageTest 102400 10 = true := by
  decide +kernel

private theorem block_103424_10 : checkPow stageTest 103424 10 = true := by
  decide +kernel

private theorem block_104448_10 : checkPow stageTest 104448 10 = true := by
  decide +kernel

private theorem block_105472_10 : checkPow stageTest 105472 10 = true := by
  decide +kernel

private theorem block_106496_10 : checkPow stageTest 106496 10 = true := by
  decide +kernel

private theorem block_107520_10 : checkPow stageTest 107520 10 = true := by
  decide +kernel

private theorem block_108544_10 : checkPow stageTest 108544 10 = true := by
  decide +kernel

private theorem block_109568_10 : checkPow stageTest 109568 10 = true := by
  decide +kernel

private theorem block_110592_10 : checkPow stageTest 110592 10 = true := by
  decide +kernel

private theorem block_111616_10 : checkPow stageTest 111616 10 = true := by
  decide +kernel

private theorem block_112640_10 : checkPow stageTest 112640 10 = true := by
  decide +kernel

private theorem block_113664_10 : checkPow stageTest 113664 10 = true := by
  decide +kernel

private theorem block_114688_10 : checkPow stageTest 114688 10 = true := by
  decide +kernel

private theorem block_115712_10 : checkPow stageTest 115712 10 = true := by
  decide +kernel

private theorem block_116736_10 : checkPow stageTest 116736 10 = true := by
  decide +kernel

private theorem block_117760_10 : checkPow stageTest 117760 10 = true := by
  decide +kernel

private theorem block_118784_10 : checkPow stageTest 118784 10 = true := by
  decide +kernel

private theorem block_119808_10 : checkPow stageTest 119808 10 = true := by
  decide +kernel

private theorem block_120832_10 : checkPow stageTest 120832 10 = true := by
  decide +kernel

private theorem block_121856_10 : checkPow stageTest 121856 10 = true := by
  decide +kernel

private theorem block_122880_10 : checkPow stageTest 122880 10 = true := by
  decide +kernel

private theorem block_123904_10 : checkPow stageTest 123904 10 = true := by
  decide +kernel

private theorem block_124928_10 : checkPow stageTest 124928 10 = true := by
  decide +kernel

private theorem block_125952_10 : checkPow stageTest 125952 10 = true := by
  decide +kernel

private theorem block_126976_10 : checkPow stageTest 126976 10 = true := by
  decide +kernel

private theorem block_128000_10 : checkPow stageTest 128000 10 = true := by
  decide +kernel

private theorem block_129024_10 : checkPow stageTest 129024 10 = true := by
  decide +kernel

private theorem block_130048_10 : checkPow stageTest 130048 10 = true := by
  decide +kernel

private theorem block_131072_10 : checkPow stageTest 131072 10 = true := by
  decide +kernel

private theorem block_132096_10 : checkPow stageTest 132096 10 = true := by
  decide +kernel

private theorem block_133120_10 : checkPow stageTest 133120 10 = true := by
  decide +kernel

private theorem block_134144_10 : checkPow stageTest 134144 10 = true := by
  decide +kernel

private theorem block_135168_10 : checkPow stageTest 135168 10 = true := by
  decide +kernel

private theorem block_136192_10 : checkPow stageTest 136192 10 = true := by
  decide +kernel

private theorem block_137216_10 : checkPow stageTest 137216 10 = true := by
  decide +kernel

private theorem block_138240_10 : checkPow stageTest 138240 10 = true := by
  decide +kernel

private theorem block_139264_10 : checkPow stageTest 139264 10 = true := by
  decide +kernel

private theorem block_140288_10 : checkPow stageTest 140288 10 = true := by
  decide +kernel

private theorem block_141312_10 : checkPow stageTest 141312 10 = true := by
  decide +kernel

private theorem block_142336_10 : checkPow stageTest 142336 10 = true := by
  decide +kernel

private theorem block_143360_10 : checkPow stageTest 143360 10 = true := by
  decide +kernel

private theorem block_144384_10 : checkPow stageTest 144384 10 = true := by
  decide +kernel

private theorem block_145408_10 : checkPow stageTest 145408 10 = true := by
  decide +kernel

private theorem block_146432_10 : checkPow stageTest 146432 10 = true := by
  decide +kernel

private theorem block_147456_10 : checkPow stageTest 147456 10 = true := by
  decide +kernel

private theorem block_148480_10 : checkPow stageTest 148480 10 = true := by
  decide +kernel

private theorem block_149504_10 : checkPow stageTest 149504 10 = true := by
  decide +kernel

private theorem block_150528_10 : checkPow stageTest 150528 10 = true := by
  decide +kernel

private theorem block_151552_10 : checkPow stageTest 151552 10 = true := by
  decide +kernel

private theorem block_152576_10 : checkPow stageTest 152576 10 = true := by
  decide +kernel

private theorem block_153600_10 : checkPow stageTest 153600 10 = true := by
  decide +kernel

private theorem block_154624_10 : checkPow stageTest 154624 10 = true := by
  decide +kernel

private theorem block_155648_10 : checkPow stageTest 155648 10 = true := by
  decide +kernel

private theorem block_156672_10 : checkPow stageTest 156672 10 = true := by
  decide +kernel

private theorem block_157696_10 : checkPow stageTest 157696 10 = true := by
  decide +kernel

private theorem block_158720_10 : checkPow stageTest 158720 10 = true := by
  decide +kernel

private theorem block_159744_10 : checkPow stageTest 159744 10 = true := by
  decide +kernel

private theorem block_160768_10 : checkPow stageTest 160768 10 = true := by
  decide +kernel

private theorem block_161792_10 : checkPow stageTest 161792 10 = true := by
  decide +kernel

private theorem block_162816_10 : checkPow stageTest 162816 10 = true := by
  decide +kernel

private theorem block_163840_10 : checkPow stageTest 163840 10 = true := by
  decide +kernel

private theorem block_164864_10 : checkPow stageTest 164864 10 = true := by
  decide +kernel

private theorem block_165888_10 : checkPow stageTest 165888 10 = true := by
  decide +kernel

private theorem block_166912_10 : checkPow stageTest 166912 10 = true := by
  decide +kernel

private theorem block_167936_10 : checkPow stageTest 167936 10 = true := by
  decide +kernel

private theorem block_168960_10 : checkPow stageTest 168960 10 = true := by
  decide +kernel

private theorem block_169984_10 : checkPow stageTest 169984 10 = true := by
  decide +kernel

private theorem block_171008_10 : checkPow stageTest 171008 10 = true := by
  decide +kernel

private theorem block_172032_10 : checkPow stageTest 172032 10 = true := by
  decide +kernel

private theorem block_173056_10 : checkPow stageTest 173056 10 = true := by
  decide +kernel

private theorem block_174080_10 : checkPow stageTest 174080 10 = true := by
  decide +kernel

private theorem block_175104_10 : checkPow stageTest 175104 10 = true := by
  decide +kernel

private theorem block_176128_10 : checkPow stageTest 176128 10 = true := by
  decide +kernel

private theorem block_177152_10 : checkPow stageTest 177152 10 = true := by
  decide +kernel

private theorem block_178176_10 : checkPow stageTest 178176 10 = true := by
  decide +kernel

private theorem block_179200_10 : checkPow stageTest 179200 10 = true := by
  decide +kernel

private theorem block_180224_10 : checkPow stageTest 180224 10 = true := by
  decide +kernel

private theorem block_181248_10 : checkPow stageTest 181248 10 = true := by
  decide +kernel

private theorem block_182272_10 : checkPow stageTest 182272 10 = true := by
  decide +kernel

private theorem block_183296_10 : checkPow stageTest 183296 10 = true := by
  decide +kernel

private theorem block_184320_10 : checkPow stageTest 184320 10 = true := by
  decide +kernel

private theorem block_185344_10 : checkPow stageTest 185344 10 = true := by
  decide +kernel

private theorem block_186368_10 : checkPow stageTest 186368 10 = true := by
  decide +kernel

private theorem block_187392_10 : checkPow stageTest 187392 10 = true := by
  decide +kernel

private theorem block_188416_10 : checkPow stageTest 188416 10 = true := by
  decide +kernel

private theorem block_189440_10 : checkPow stageTest 189440 10 = true := by
  decide +kernel

private theorem block_190464_10 : checkPow stageTest 190464 10 = true := by
  decide +kernel

private theorem block_191488_10 : checkPow stageTest 191488 10 = true := by
  decide +kernel

private theorem block_192512_10 : checkPow stageTest 192512 10 = true := by
  decide +kernel

private theorem block_193536_10 : checkPow stageTest 193536 10 = true := by
  decide +kernel

private theorem block_194560_10 : checkPow stageTest 194560 10 = true := by
  decide +kernel

private theorem block_195584_10 : checkPow stageTest 195584 10 = true := by
  decide +kernel

private theorem block_196608_10 : checkPow stageTest 196608 10 = true := by
  decide +kernel

private theorem block_197632_10 : checkPow stageTest 197632 10 = true := by
  decide +kernel

private theorem block_198656_10 : checkPow stageTest 198656 10 = true := by
  decide +kernel

private theorem block_199680_10 : checkPow stageTest 199680 10 = true := by
  decide +kernel

private theorem block_200704_10 : checkPow stageTest 200704 10 = true := by
  decide +kernel

private theorem block_201728_10 : checkPow stageTest 201728 10 = true := by
  decide +kernel

private theorem block_202752_10 : checkPow stageTest 202752 10 = true := by
  decide +kernel

private theorem block_203776_10 : checkPow stageTest 203776 10 = true := by
  decide +kernel

private theorem block_204800_10 : checkPow stageTest 204800 10 = true := by
  decide +kernel

private theorem block_205824_10 : checkPow stageTest 205824 10 = true := by
  decide +kernel

private theorem block_206848_10 : checkPow stageTest 206848 10 = true := by
  decide +kernel

private theorem block_207872_10 : checkPow stageTest 207872 10 = true := by
  decide +kernel

private theorem block_208896_10 : checkPow stageTest 208896 10 = true := by
  decide +kernel

private theorem block_209920_10 : checkPow stageTest 209920 10 = true := by
  decide +kernel

private theorem block_210944_10 : checkPow stageTest 210944 10 = true := by
  decide +kernel

private theorem block_211968_10 : checkPow stageTest 211968 10 = true := by
  decide +kernel

private theorem block_212992_10 : checkPow stageTest 212992 10 = true := by
  decide +kernel

private theorem block_214016_10 : checkPow stageTest 214016 10 = true := by
  decide +kernel

private theorem block_215040_10 : checkPow stageTest 215040 10 = true := by
  decide +kernel

private theorem block_216064_10 : checkPow stageTest 216064 10 = true := by
  decide +kernel

private theorem block_217088_10 : checkPow stageTest 217088 10 = true := by
  decide +kernel

private theorem block_218112_10 : checkPow stageTest 218112 10 = true := by
  decide +kernel

private theorem block_219136_10 : checkPow stageTest 219136 10 = true := by
  decide +kernel

private theorem block_220160_10 : checkPow stageTest 220160 10 = true := by
  decide +kernel

private theorem block_221184_10 : checkPow stageTest 221184 10 = true := by
  decide +kernel

private theorem block_222208_10 : checkPow stageTest 222208 10 = true := by
  decide +kernel

private theorem block_223232_10 : checkPow stageTest 223232 10 = true := by
  decide +kernel

private theorem block_224256_10 : checkPow stageTest 224256 10 = true := by
  decide +kernel

private theorem block_225280_10 : checkPow stageTest 225280 10 = true := by
  decide +kernel

private theorem block_226304_10 : checkPow stageTest 226304 10 = true := by
  decide +kernel

private theorem block_227328_10 : checkPow stageTest 227328 10 = true := by
  decide +kernel

private theorem block_228352_10 : checkPow stageTest 228352 10 = true := by
  decide +kernel

private theorem block_229376_10 : checkPow stageTest 229376 10 = true := by
  decide +kernel

private theorem block_230400_10 : checkPow stageTest 230400 10 = true := by
  decide +kernel

private theorem block_231424_10 : checkPow stageTest 231424 10 = true := by
  decide +kernel

private theorem block_232448_10 : checkPow stageTest 232448 10 = true := by
  decide +kernel

private theorem block_233472_10 : checkPow stageTest 233472 10 = true := by
  decide +kernel

private theorem block_234496_10 : checkPow stageTest 234496 10 = true := by
  decide +kernel

private theorem block_235520_10 : checkPow stageTest 235520 10 = true := by
  decide +kernel

private theorem block_236544_10 : checkPow stageTest 236544 10 = true := by
  decide +kernel

private theorem block_237568_10 : checkPow stageTest 237568 10 = true := by
  decide +kernel

private theorem block_238592_10 : checkPow stageTest 238592 10 = true := by
  decide +kernel

private theorem block_239616_10 : checkPow stageTest 239616 10 = true := by
  decide +kernel

private theorem block_240640_10 : checkPow stageTest 240640 10 = true := by
  decide +kernel

private theorem block_241664_10 : checkPow stageTest 241664 10 = true := by
  decide +kernel

private theorem block_242688_10 : checkPow stageTest 242688 10 = true := by
  decide +kernel

private theorem block_243712_10 : checkPow stageTest 243712 10 = true := by
  decide +kernel

private theorem block_244736_10 : checkPow stageTest 244736 10 = true := by
  decide +kernel

private theorem block_245760_10 : checkPow stageTest 245760 10 = true := by
  decide +kernel

private theorem block_246784_10 : checkPow stageTest 246784 10 = true := by
  decide +kernel

private theorem block_247808_10 : checkPow stageTest 247808 10 = true := by
  decide +kernel

private theorem block_248832_10 : checkPow stageTest 248832 10 = true := by
  decide +kernel

private theorem block_249856_10 : checkPow stageTest 249856 10 = true := by
  decide +kernel

private theorem block_250880_10 : checkPow stageTest 250880 10 = true := by
  decide +kernel

private theorem block_251904_10 : checkPow stageTest 251904 10 = true := by
  decide +kernel

private theorem block_252928_10 : checkPow stageTest 252928 10 = true := by
  decide +kernel

private theorem block_253952_10 : checkPow stageTest 253952 10 = true := by
  decide +kernel

private theorem block_254976_10 : checkPow stageTest 254976 10 = true := by
  decide +kernel

private theorem block_256000_10 : checkPow stageTest 256000 10 = true := by
  decide +kernel

private theorem block_257024_10 : checkPow stageTest 257024 10 = true := by
  decide +kernel

private theorem block_258048_10 : checkPow stageTest 258048 10 = true := by
  decide +kernel

private theorem block_259072_10 : checkPow stageTest 259072 10 = true := by
  decide +kernel

private theorem block_260096_10 : checkPow stageTest 260096 10 = true := by
  decide +kernel

private theorem block_261120_10 : checkPow stageTest 261120 10 = true := by
  decide +kernel

private theorem block_262144_10 : checkPow stageTest 262144 10 = true := by
  decide +kernel

private theorem block_263168_10 : checkPow stageTest 263168 10 = true := by
  decide +kernel

private theorem block_264192_10 : checkPow stageTest 264192 10 = true := by
  decide +kernel

private theorem block_265216_10 : checkPow stageTest 265216 10 = true := by
  decide +kernel

private theorem block_266240_10 : checkPow stageTest 266240 10 = true := by
  decide +kernel

private theorem block_267264_10 : checkPow stageTest 267264 10 = true := by
  decide +kernel

private theorem block_268288_10 : checkPow stageTest 268288 10 = true := by
  decide +kernel

private theorem block_269312_10 : checkPow stageTest 269312 10 = true := by
  decide +kernel

private theorem block_270336_10 : checkPow stageTest 270336 10 = true := by
  decide +kernel

private theorem block_271360_10 : checkPow stageTest 271360 10 = true := by
  decide +kernel

private theorem block_272384_10 : checkPow stageTest 272384 10 = true := by
  decide +kernel

private theorem block_273408_10 : checkPow stageTest 273408 10 = true := by
  decide +kernel

private theorem block_274432_10 : checkPow stageTest 274432 10 = true := by
  decide +kernel

private theorem block_275456_10 : checkPow stageTest 275456 10 = true := by
  decide +kernel

private theorem block_276480_10 : checkPow stageTest 276480 10 = true := by
  decide +kernel

private theorem block_277504_10 : checkPow stageTest 277504 10 = true := by
  decide +kernel

private theorem block_278528_10 : checkPow stageTest 278528 10 = true := by
  decide +kernel

private theorem block_279552_10 : checkPow stageTest 279552 10 = true := by
  decide +kernel

private theorem block_280576_10 : checkPow stageTest 280576 10 = true := by
  decide +kernel

private theorem block_281600_10 : checkPow stageTest 281600 10 = true := by
  decide +kernel

private theorem block_282624_10 : checkPow stageTest 282624 10 = true := by
  decide +kernel

private theorem block_283648_10 : checkPow stageTest 283648 10 = true := by
  decide +kernel

private theorem block_284672_10 : checkPow stageTest 284672 10 = true := by
  decide +kernel

private theorem block_285696_10 : checkPow stageTest 285696 10 = true := by
  decide +kernel

private theorem block_286720_10 : checkPow stageTest 286720 10 = true := by
  decide +kernel

private theorem block_287744_10 : checkPow stageTest 287744 10 = true := by
  decide +kernel

private theorem block_288768_10 : checkPow stageTest 288768 10 = true := by
  decide +kernel

private theorem block_289792_10 : checkPow stageTest 289792 10 = true := by
  decide +kernel

private theorem block_290816_10 : checkPow stageTest 290816 10 = true := by
  decide +kernel

private theorem block_291840_10 : checkPow stageTest 291840 10 = true := by
  decide +kernel

private theorem block_292864_10 : checkPow stageTest 292864 10 = true := by
  decide +kernel

private theorem block_293888_10 : checkPow stageTest 293888 10 = true := by
  decide +kernel

private theorem block_294912_10 : checkPow stageTest 294912 10 = true := by
  decide +kernel

private theorem block_295936_10 : checkPow stageTest 295936 10 = true := by
  decide +kernel

private theorem block_296960_10 : checkPow stageTest 296960 10 = true := by
  decide +kernel

private theorem block_297984_10 : checkPow stageTest 297984 10 = true := by
  decide +kernel

private theorem block_299008_10 : checkPow stageTest 299008 10 = true := by
  decide +kernel

private theorem block_300032_10 : checkPow stageTest 300032 10 = true := by
  decide +kernel

private theorem block_301056_10 : checkPow stageTest 301056 10 = true := by
  decide +kernel

private theorem block_302080_10 : checkPow stageTest 302080 10 = true := by
  decide +kernel

private theorem block_303104_10 : checkPow stageTest 303104 10 = true := by
  decide +kernel

private theorem block_304128_10 : checkPow stageTest 304128 10 = true := by
  decide +kernel

private theorem block_305152_10 : checkPow stageTest 305152 10 = true := by
  decide +kernel

private theorem block_306176_10 : checkPow stageTest 306176 10 = true := by
  decide +kernel

private theorem block_0_11 : checkPow stageTest 0 11 = true :=
  checkPow_join stageTest 10 0 block_0_10 block_1024_10

private theorem block_2048_11 : checkPow stageTest 2048 11 = true :=
  checkPow_join stageTest 10 2048 block_2048_10 block_3072_10

private theorem block_4096_11 : checkPow stageTest 4096 11 = true :=
  checkPow_join stageTest 10 4096 block_4096_10 block_5120_10

private theorem block_6144_11 : checkPow stageTest 6144 11 = true :=
  checkPow_join stageTest 10 6144 block_6144_10 block_7168_10

private theorem block_8192_11 : checkPow stageTest 8192 11 = true :=
  checkPow_join stageTest 10 8192 block_8192_10 block_9216_10

private theorem block_10240_11 : checkPow stageTest 10240 11 = true :=
  checkPow_join stageTest 10 10240 block_10240_10 block_11264_10

private theorem block_12288_11 : checkPow stageTest 12288 11 = true :=
  checkPow_join stageTest 10 12288 block_12288_10 block_13312_10

private theorem block_14336_11 : checkPow stageTest 14336 11 = true :=
  checkPow_join stageTest 10 14336 block_14336_10 block_15360_10

private theorem block_16384_11 : checkPow stageTest 16384 11 = true :=
  checkPow_join stageTest 10 16384 block_16384_10 block_17408_10

private theorem block_18432_11 : checkPow stageTest 18432 11 = true :=
  checkPow_join stageTest 10 18432 block_18432_10 block_19456_10

private theorem block_20480_11 : checkPow stageTest 20480 11 = true :=
  checkPow_join stageTest 10 20480 block_20480_10 block_21504_10

private theorem block_22528_11 : checkPow stageTest 22528 11 = true :=
  checkPow_join stageTest 10 22528 block_22528_10 block_23552_10

private theorem block_24576_11 : checkPow stageTest 24576 11 = true :=
  checkPow_join stageTest 10 24576 block_24576_10 block_25600_10

private theorem block_26624_11 : checkPow stageTest 26624 11 = true :=
  checkPow_join stageTest 10 26624 block_26624_10 block_27648_10

private theorem block_28672_11 : checkPow stageTest 28672 11 = true :=
  checkPow_join stageTest 10 28672 block_28672_10 block_29696_10

private theorem block_30720_11 : checkPow stageTest 30720 11 = true :=
  checkPow_join stageTest 10 30720 block_30720_10 block_31744_10

private theorem block_32768_11 : checkPow stageTest 32768 11 = true :=
  checkPow_join stageTest 10 32768 block_32768_10 block_33792_10

private theorem block_34816_11 : checkPow stageTest 34816 11 = true :=
  checkPow_join stageTest 10 34816 block_34816_10 block_35840_10

private theorem block_36864_11 : checkPow stageTest 36864 11 = true :=
  checkPow_join stageTest 10 36864 block_36864_10 block_37888_10

private theorem block_38912_11 : checkPow stageTest 38912 11 = true :=
  checkPow_join stageTest 10 38912 block_38912_10 block_39936_10

private theorem block_40960_11 : checkPow stageTest 40960 11 = true :=
  checkPow_join stageTest 10 40960 block_40960_10 block_41984_10

private theorem block_43008_11 : checkPow stageTest 43008 11 = true :=
  checkPow_join stageTest 10 43008 block_43008_10 block_44032_10

private theorem block_45056_11 : checkPow stageTest 45056 11 = true :=
  checkPow_join stageTest 10 45056 block_45056_10 block_46080_10

private theorem block_47104_11 : checkPow stageTest 47104 11 = true :=
  checkPow_join stageTest 10 47104 block_47104_10 block_48128_10

private theorem block_49152_11 : checkPow stageTest 49152 11 = true :=
  checkPow_join stageTest 10 49152 block_49152_10 block_50176_10

private theorem block_51200_11 : checkPow stageTest 51200 11 = true :=
  checkPow_join stageTest 10 51200 block_51200_10 block_52224_10

private theorem block_53248_11 : checkPow stageTest 53248 11 = true :=
  checkPow_join stageTest 10 53248 block_53248_10 block_54272_10

private theorem block_55296_11 : checkPow stageTest 55296 11 = true :=
  checkPow_join stageTest 10 55296 block_55296_10 block_56320_10

private theorem block_57344_11 : checkPow stageTest 57344 11 = true :=
  checkPow_join stageTest 10 57344 block_57344_10 block_58368_10

private theorem block_59392_11 : checkPow stageTest 59392 11 = true :=
  checkPow_join stageTest 10 59392 block_59392_10 block_60416_10

private theorem block_61440_11 : checkPow stageTest 61440 11 = true :=
  checkPow_join stageTest 10 61440 block_61440_10 block_62464_10

private theorem block_63488_11 : checkPow stageTest 63488 11 = true :=
  checkPow_join stageTest 10 63488 block_63488_10 block_64512_10

private theorem block_65536_11 : checkPow stageTest 65536 11 = true :=
  checkPow_join stageTest 10 65536 block_65536_10 block_66560_10

private theorem block_67584_11 : checkPow stageTest 67584 11 = true :=
  checkPow_join stageTest 10 67584 block_67584_10 block_68608_10

private theorem block_69632_11 : checkPow stageTest 69632 11 = true :=
  checkPow_join stageTest 10 69632 block_69632_10 block_70656_10

private theorem block_71680_11 : checkPow stageTest 71680 11 = true :=
  checkPow_join stageTest 10 71680 block_71680_10 block_72704_10

private theorem block_73728_11 : checkPow stageTest 73728 11 = true :=
  checkPow_join stageTest 10 73728 block_73728_10 block_74752_10

private theorem block_75776_11 : checkPow stageTest 75776 11 = true :=
  checkPow_join stageTest 10 75776 block_75776_10 block_76800_10

private theorem block_77824_11 : checkPow stageTest 77824 11 = true :=
  checkPow_join stageTest 10 77824 block_77824_10 block_78848_10

private theorem block_79872_11 : checkPow stageTest 79872 11 = true :=
  checkPow_join stageTest 10 79872 block_79872_10 block_80896_10

private theorem block_81920_11 : checkPow stageTest 81920 11 = true :=
  checkPow_join stageTest 10 81920 block_81920_10 block_82944_10

private theorem block_83968_11 : checkPow stageTest 83968 11 = true :=
  checkPow_join stageTest 10 83968 block_83968_10 block_84992_10

private theorem block_86016_11 : checkPow stageTest 86016 11 = true :=
  checkPow_join stageTest 10 86016 block_86016_10 block_87040_10

private theorem block_88064_11 : checkPow stageTest 88064 11 = true :=
  checkPow_join stageTest 10 88064 block_88064_10 block_89088_10

private theorem block_90112_11 : checkPow stageTest 90112 11 = true :=
  checkPow_join stageTest 10 90112 block_90112_10 block_91136_10

private theorem block_92160_11 : checkPow stageTest 92160 11 = true :=
  checkPow_join stageTest 10 92160 block_92160_10 block_93184_10

private theorem block_94208_11 : checkPow stageTest 94208 11 = true :=
  checkPow_join stageTest 10 94208 block_94208_10 block_95232_10

private theorem block_96256_11 : checkPow stageTest 96256 11 = true :=
  checkPow_join stageTest 10 96256 block_96256_10 block_97280_10

private theorem block_98304_11 : checkPow stageTest 98304 11 = true :=
  checkPow_join stageTest 10 98304 block_98304_10 block_99328_10

private theorem block_100352_11 : checkPow stageTest 100352 11 = true :=
  checkPow_join stageTest 10 100352 block_100352_10 block_101376_10

private theorem block_102400_11 : checkPow stageTest 102400 11 = true :=
  checkPow_join stageTest 10 102400 block_102400_10 block_103424_10

private theorem block_104448_11 : checkPow stageTest 104448 11 = true :=
  checkPow_join stageTest 10 104448 block_104448_10 block_105472_10

private theorem block_106496_11 : checkPow stageTest 106496 11 = true :=
  checkPow_join stageTest 10 106496 block_106496_10 block_107520_10

private theorem block_108544_11 : checkPow stageTest 108544 11 = true :=
  checkPow_join stageTest 10 108544 block_108544_10 block_109568_10

private theorem block_110592_11 : checkPow stageTest 110592 11 = true :=
  checkPow_join stageTest 10 110592 block_110592_10 block_111616_10

private theorem block_112640_11 : checkPow stageTest 112640 11 = true :=
  checkPow_join stageTest 10 112640 block_112640_10 block_113664_10

private theorem block_114688_11 : checkPow stageTest 114688 11 = true :=
  checkPow_join stageTest 10 114688 block_114688_10 block_115712_10

private theorem block_116736_11 : checkPow stageTest 116736 11 = true :=
  checkPow_join stageTest 10 116736 block_116736_10 block_117760_10

private theorem block_118784_11 : checkPow stageTest 118784 11 = true :=
  checkPow_join stageTest 10 118784 block_118784_10 block_119808_10

private theorem block_120832_11 : checkPow stageTest 120832 11 = true :=
  checkPow_join stageTest 10 120832 block_120832_10 block_121856_10

private theorem block_122880_11 : checkPow stageTest 122880 11 = true :=
  checkPow_join stageTest 10 122880 block_122880_10 block_123904_10

private theorem block_124928_11 : checkPow stageTest 124928 11 = true :=
  checkPow_join stageTest 10 124928 block_124928_10 block_125952_10

private theorem block_126976_11 : checkPow stageTest 126976 11 = true :=
  checkPow_join stageTest 10 126976 block_126976_10 block_128000_10

private theorem block_129024_11 : checkPow stageTest 129024 11 = true :=
  checkPow_join stageTest 10 129024 block_129024_10 block_130048_10

private theorem block_131072_11 : checkPow stageTest 131072 11 = true :=
  checkPow_join stageTest 10 131072 block_131072_10 block_132096_10

private theorem block_133120_11 : checkPow stageTest 133120 11 = true :=
  checkPow_join stageTest 10 133120 block_133120_10 block_134144_10

private theorem block_135168_11 : checkPow stageTest 135168 11 = true :=
  checkPow_join stageTest 10 135168 block_135168_10 block_136192_10

private theorem block_137216_11 : checkPow stageTest 137216 11 = true :=
  checkPow_join stageTest 10 137216 block_137216_10 block_138240_10

private theorem block_139264_11 : checkPow stageTest 139264 11 = true :=
  checkPow_join stageTest 10 139264 block_139264_10 block_140288_10

private theorem block_141312_11 : checkPow stageTest 141312 11 = true :=
  checkPow_join stageTest 10 141312 block_141312_10 block_142336_10

private theorem block_143360_11 : checkPow stageTest 143360 11 = true :=
  checkPow_join stageTest 10 143360 block_143360_10 block_144384_10

private theorem block_145408_11 : checkPow stageTest 145408 11 = true :=
  checkPow_join stageTest 10 145408 block_145408_10 block_146432_10

private theorem block_147456_11 : checkPow stageTest 147456 11 = true :=
  checkPow_join stageTest 10 147456 block_147456_10 block_148480_10

private theorem block_149504_11 : checkPow stageTest 149504 11 = true :=
  checkPow_join stageTest 10 149504 block_149504_10 block_150528_10

private theorem block_151552_11 : checkPow stageTest 151552 11 = true :=
  checkPow_join stageTest 10 151552 block_151552_10 block_152576_10

private theorem block_153600_11 : checkPow stageTest 153600 11 = true :=
  checkPow_join stageTest 10 153600 block_153600_10 block_154624_10

private theorem block_155648_11 : checkPow stageTest 155648 11 = true :=
  checkPow_join stageTest 10 155648 block_155648_10 block_156672_10

private theorem block_157696_11 : checkPow stageTest 157696 11 = true :=
  checkPow_join stageTest 10 157696 block_157696_10 block_158720_10

private theorem block_159744_11 : checkPow stageTest 159744 11 = true :=
  checkPow_join stageTest 10 159744 block_159744_10 block_160768_10

private theorem block_161792_11 : checkPow stageTest 161792 11 = true :=
  checkPow_join stageTest 10 161792 block_161792_10 block_162816_10

private theorem block_163840_11 : checkPow stageTest 163840 11 = true :=
  checkPow_join stageTest 10 163840 block_163840_10 block_164864_10

private theorem block_165888_11 : checkPow stageTest 165888 11 = true :=
  checkPow_join stageTest 10 165888 block_165888_10 block_166912_10

private theorem block_167936_11 : checkPow stageTest 167936 11 = true :=
  checkPow_join stageTest 10 167936 block_167936_10 block_168960_10

private theorem block_169984_11 : checkPow stageTest 169984 11 = true :=
  checkPow_join stageTest 10 169984 block_169984_10 block_171008_10

private theorem block_172032_11 : checkPow stageTest 172032 11 = true :=
  checkPow_join stageTest 10 172032 block_172032_10 block_173056_10

private theorem block_174080_11 : checkPow stageTest 174080 11 = true :=
  checkPow_join stageTest 10 174080 block_174080_10 block_175104_10

private theorem block_176128_11 : checkPow stageTest 176128 11 = true :=
  checkPow_join stageTest 10 176128 block_176128_10 block_177152_10

private theorem block_178176_11 : checkPow stageTest 178176 11 = true :=
  checkPow_join stageTest 10 178176 block_178176_10 block_179200_10

private theorem block_180224_11 : checkPow stageTest 180224 11 = true :=
  checkPow_join stageTest 10 180224 block_180224_10 block_181248_10

private theorem block_182272_11 : checkPow stageTest 182272 11 = true :=
  checkPow_join stageTest 10 182272 block_182272_10 block_183296_10

private theorem block_184320_11 : checkPow stageTest 184320 11 = true :=
  checkPow_join stageTest 10 184320 block_184320_10 block_185344_10

private theorem block_186368_11 : checkPow stageTest 186368 11 = true :=
  checkPow_join stageTest 10 186368 block_186368_10 block_187392_10

private theorem block_188416_11 : checkPow stageTest 188416 11 = true :=
  checkPow_join stageTest 10 188416 block_188416_10 block_189440_10

private theorem block_190464_11 : checkPow stageTest 190464 11 = true :=
  checkPow_join stageTest 10 190464 block_190464_10 block_191488_10

private theorem block_192512_11 : checkPow stageTest 192512 11 = true :=
  checkPow_join stageTest 10 192512 block_192512_10 block_193536_10

private theorem block_194560_11 : checkPow stageTest 194560 11 = true :=
  checkPow_join stageTest 10 194560 block_194560_10 block_195584_10

private theorem block_196608_11 : checkPow stageTest 196608 11 = true :=
  checkPow_join stageTest 10 196608 block_196608_10 block_197632_10

private theorem block_198656_11 : checkPow stageTest 198656 11 = true :=
  checkPow_join stageTest 10 198656 block_198656_10 block_199680_10

private theorem block_200704_11 : checkPow stageTest 200704 11 = true :=
  checkPow_join stageTest 10 200704 block_200704_10 block_201728_10

private theorem block_202752_11 : checkPow stageTest 202752 11 = true :=
  checkPow_join stageTest 10 202752 block_202752_10 block_203776_10

private theorem block_204800_11 : checkPow stageTest 204800 11 = true :=
  checkPow_join stageTest 10 204800 block_204800_10 block_205824_10

private theorem block_206848_11 : checkPow stageTest 206848 11 = true :=
  checkPow_join stageTest 10 206848 block_206848_10 block_207872_10

private theorem block_208896_11 : checkPow stageTest 208896 11 = true :=
  checkPow_join stageTest 10 208896 block_208896_10 block_209920_10

private theorem block_210944_11 : checkPow stageTest 210944 11 = true :=
  checkPow_join stageTest 10 210944 block_210944_10 block_211968_10

private theorem block_212992_11 : checkPow stageTest 212992 11 = true :=
  checkPow_join stageTest 10 212992 block_212992_10 block_214016_10

private theorem block_215040_11 : checkPow stageTest 215040 11 = true :=
  checkPow_join stageTest 10 215040 block_215040_10 block_216064_10

private theorem block_217088_11 : checkPow stageTest 217088 11 = true :=
  checkPow_join stageTest 10 217088 block_217088_10 block_218112_10

private theorem block_219136_11 : checkPow stageTest 219136 11 = true :=
  checkPow_join stageTest 10 219136 block_219136_10 block_220160_10

private theorem block_221184_11 : checkPow stageTest 221184 11 = true :=
  checkPow_join stageTest 10 221184 block_221184_10 block_222208_10

private theorem block_223232_11 : checkPow stageTest 223232 11 = true :=
  checkPow_join stageTest 10 223232 block_223232_10 block_224256_10

private theorem block_225280_11 : checkPow stageTest 225280 11 = true :=
  checkPow_join stageTest 10 225280 block_225280_10 block_226304_10

private theorem block_227328_11 : checkPow stageTest 227328 11 = true :=
  checkPow_join stageTest 10 227328 block_227328_10 block_228352_10

private theorem block_229376_11 : checkPow stageTest 229376 11 = true :=
  checkPow_join stageTest 10 229376 block_229376_10 block_230400_10

private theorem block_231424_11 : checkPow stageTest 231424 11 = true :=
  checkPow_join stageTest 10 231424 block_231424_10 block_232448_10

private theorem block_233472_11 : checkPow stageTest 233472 11 = true :=
  checkPow_join stageTest 10 233472 block_233472_10 block_234496_10

private theorem block_235520_11 : checkPow stageTest 235520 11 = true :=
  checkPow_join stageTest 10 235520 block_235520_10 block_236544_10

private theorem block_237568_11 : checkPow stageTest 237568 11 = true :=
  checkPow_join stageTest 10 237568 block_237568_10 block_238592_10

private theorem block_239616_11 : checkPow stageTest 239616 11 = true :=
  checkPow_join stageTest 10 239616 block_239616_10 block_240640_10

private theorem block_241664_11 : checkPow stageTest 241664 11 = true :=
  checkPow_join stageTest 10 241664 block_241664_10 block_242688_10

private theorem block_243712_11 : checkPow stageTest 243712 11 = true :=
  checkPow_join stageTest 10 243712 block_243712_10 block_244736_10

private theorem block_245760_11 : checkPow stageTest 245760 11 = true :=
  checkPow_join stageTest 10 245760 block_245760_10 block_246784_10

private theorem block_247808_11 : checkPow stageTest 247808 11 = true :=
  checkPow_join stageTest 10 247808 block_247808_10 block_248832_10

private theorem block_249856_11 : checkPow stageTest 249856 11 = true :=
  checkPow_join stageTest 10 249856 block_249856_10 block_250880_10

private theorem block_251904_11 : checkPow stageTest 251904 11 = true :=
  checkPow_join stageTest 10 251904 block_251904_10 block_252928_10

private theorem block_253952_11 : checkPow stageTest 253952 11 = true :=
  checkPow_join stageTest 10 253952 block_253952_10 block_254976_10

private theorem block_256000_11 : checkPow stageTest 256000 11 = true :=
  checkPow_join stageTest 10 256000 block_256000_10 block_257024_10

private theorem block_258048_11 : checkPow stageTest 258048 11 = true :=
  checkPow_join stageTest 10 258048 block_258048_10 block_259072_10

private theorem block_260096_11 : checkPow stageTest 260096 11 = true :=
  checkPow_join stageTest 10 260096 block_260096_10 block_261120_10

private theorem block_0_12 : checkPow stageTest 0 12 = true :=
  checkPow_join stageTest 11 0 block_0_11 block_2048_11

private theorem block_4096_12 : checkPow stageTest 4096 12 = true :=
  checkPow_join stageTest 11 4096 block_4096_11 block_6144_11

private theorem block_8192_12 : checkPow stageTest 8192 12 = true :=
  checkPow_join stageTest 11 8192 block_8192_11 block_10240_11

private theorem block_12288_12 : checkPow stageTest 12288 12 = true :=
  checkPow_join stageTest 11 12288 block_12288_11 block_14336_11

private theorem block_16384_12 : checkPow stageTest 16384 12 = true :=
  checkPow_join stageTest 11 16384 block_16384_11 block_18432_11

private theorem block_20480_12 : checkPow stageTest 20480 12 = true :=
  checkPow_join stageTest 11 20480 block_20480_11 block_22528_11

private theorem block_24576_12 : checkPow stageTest 24576 12 = true :=
  checkPow_join stageTest 11 24576 block_24576_11 block_26624_11

private theorem block_28672_12 : checkPow stageTest 28672 12 = true :=
  checkPow_join stageTest 11 28672 block_28672_11 block_30720_11

private theorem block_32768_12 : checkPow stageTest 32768 12 = true :=
  checkPow_join stageTest 11 32768 block_32768_11 block_34816_11

private theorem block_36864_12 : checkPow stageTest 36864 12 = true :=
  checkPow_join stageTest 11 36864 block_36864_11 block_38912_11

private theorem block_40960_12 : checkPow stageTest 40960 12 = true :=
  checkPow_join stageTest 11 40960 block_40960_11 block_43008_11

private theorem block_45056_12 : checkPow stageTest 45056 12 = true :=
  checkPow_join stageTest 11 45056 block_45056_11 block_47104_11

private theorem block_49152_12 : checkPow stageTest 49152 12 = true :=
  checkPow_join stageTest 11 49152 block_49152_11 block_51200_11

private theorem block_53248_12 : checkPow stageTest 53248 12 = true :=
  checkPow_join stageTest 11 53248 block_53248_11 block_55296_11

private theorem block_57344_12 : checkPow stageTest 57344 12 = true :=
  checkPow_join stageTest 11 57344 block_57344_11 block_59392_11

private theorem block_61440_12 : checkPow stageTest 61440 12 = true :=
  checkPow_join stageTest 11 61440 block_61440_11 block_63488_11

private theorem block_65536_12 : checkPow stageTest 65536 12 = true :=
  checkPow_join stageTest 11 65536 block_65536_11 block_67584_11

private theorem block_69632_12 : checkPow stageTest 69632 12 = true :=
  checkPow_join stageTest 11 69632 block_69632_11 block_71680_11

private theorem block_73728_12 : checkPow stageTest 73728 12 = true :=
  checkPow_join stageTest 11 73728 block_73728_11 block_75776_11

private theorem block_77824_12 : checkPow stageTest 77824 12 = true :=
  checkPow_join stageTest 11 77824 block_77824_11 block_79872_11

private theorem block_81920_12 : checkPow stageTest 81920 12 = true :=
  checkPow_join stageTest 11 81920 block_81920_11 block_83968_11

private theorem block_86016_12 : checkPow stageTest 86016 12 = true :=
  checkPow_join stageTest 11 86016 block_86016_11 block_88064_11

private theorem block_90112_12 : checkPow stageTest 90112 12 = true :=
  checkPow_join stageTest 11 90112 block_90112_11 block_92160_11

private theorem block_94208_12 : checkPow stageTest 94208 12 = true :=
  checkPow_join stageTest 11 94208 block_94208_11 block_96256_11

private theorem block_98304_12 : checkPow stageTest 98304 12 = true :=
  checkPow_join stageTest 11 98304 block_98304_11 block_100352_11

private theorem block_102400_12 : checkPow stageTest 102400 12 = true :=
  checkPow_join stageTest 11 102400 block_102400_11 block_104448_11

private theorem block_106496_12 : checkPow stageTest 106496 12 = true :=
  checkPow_join stageTest 11 106496 block_106496_11 block_108544_11

private theorem block_110592_12 : checkPow stageTest 110592 12 = true :=
  checkPow_join stageTest 11 110592 block_110592_11 block_112640_11

private theorem block_114688_12 : checkPow stageTest 114688 12 = true :=
  checkPow_join stageTest 11 114688 block_114688_11 block_116736_11

private theorem block_118784_12 : checkPow stageTest 118784 12 = true :=
  checkPow_join stageTest 11 118784 block_118784_11 block_120832_11

private theorem block_122880_12 : checkPow stageTest 122880 12 = true :=
  checkPow_join stageTest 11 122880 block_122880_11 block_124928_11

private theorem block_126976_12 : checkPow stageTest 126976 12 = true :=
  checkPow_join stageTest 11 126976 block_126976_11 block_129024_11

private theorem block_131072_12 : checkPow stageTest 131072 12 = true :=
  checkPow_join stageTest 11 131072 block_131072_11 block_133120_11

private theorem block_135168_12 : checkPow stageTest 135168 12 = true :=
  checkPow_join stageTest 11 135168 block_135168_11 block_137216_11

private theorem block_139264_12 : checkPow stageTest 139264 12 = true :=
  checkPow_join stageTest 11 139264 block_139264_11 block_141312_11

private theorem block_143360_12 : checkPow stageTest 143360 12 = true :=
  checkPow_join stageTest 11 143360 block_143360_11 block_145408_11

private theorem block_147456_12 : checkPow stageTest 147456 12 = true :=
  checkPow_join stageTest 11 147456 block_147456_11 block_149504_11

private theorem block_151552_12 : checkPow stageTest 151552 12 = true :=
  checkPow_join stageTest 11 151552 block_151552_11 block_153600_11

private theorem block_155648_12 : checkPow stageTest 155648 12 = true :=
  checkPow_join stageTest 11 155648 block_155648_11 block_157696_11

private theorem block_159744_12 : checkPow stageTest 159744 12 = true :=
  checkPow_join stageTest 11 159744 block_159744_11 block_161792_11

private theorem block_163840_12 : checkPow stageTest 163840 12 = true :=
  checkPow_join stageTest 11 163840 block_163840_11 block_165888_11

private theorem block_167936_12 : checkPow stageTest 167936 12 = true :=
  checkPow_join stageTest 11 167936 block_167936_11 block_169984_11

private theorem block_172032_12 : checkPow stageTest 172032 12 = true :=
  checkPow_join stageTest 11 172032 block_172032_11 block_174080_11

private theorem block_176128_12 : checkPow stageTest 176128 12 = true :=
  checkPow_join stageTest 11 176128 block_176128_11 block_178176_11

private theorem block_180224_12 : checkPow stageTest 180224 12 = true :=
  checkPow_join stageTest 11 180224 block_180224_11 block_182272_11

private theorem block_184320_12 : checkPow stageTest 184320 12 = true :=
  checkPow_join stageTest 11 184320 block_184320_11 block_186368_11

private theorem block_188416_12 : checkPow stageTest 188416 12 = true :=
  checkPow_join stageTest 11 188416 block_188416_11 block_190464_11

private theorem block_192512_12 : checkPow stageTest 192512 12 = true :=
  checkPow_join stageTest 11 192512 block_192512_11 block_194560_11

private theorem block_196608_12 : checkPow stageTest 196608 12 = true :=
  checkPow_join stageTest 11 196608 block_196608_11 block_198656_11

private theorem block_200704_12 : checkPow stageTest 200704 12 = true :=
  checkPow_join stageTest 11 200704 block_200704_11 block_202752_11

private theorem block_204800_12 : checkPow stageTest 204800 12 = true :=
  checkPow_join stageTest 11 204800 block_204800_11 block_206848_11

private theorem block_208896_12 : checkPow stageTest 208896 12 = true :=
  checkPow_join stageTest 11 208896 block_208896_11 block_210944_11

private theorem block_212992_12 : checkPow stageTest 212992 12 = true :=
  checkPow_join stageTest 11 212992 block_212992_11 block_215040_11

private theorem block_217088_12 : checkPow stageTest 217088 12 = true :=
  checkPow_join stageTest 11 217088 block_217088_11 block_219136_11

private theorem block_221184_12 : checkPow stageTest 221184 12 = true :=
  checkPow_join stageTest 11 221184 block_221184_11 block_223232_11

private theorem block_225280_12 : checkPow stageTest 225280 12 = true :=
  checkPow_join stageTest 11 225280 block_225280_11 block_227328_11

private theorem block_229376_12 : checkPow stageTest 229376 12 = true :=
  checkPow_join stageTest 11 229376 block_229376_11 block_231424_11

private theorem block_233472_12 : checkPow stageTest 233472 12 = true :=
  checkPow_join stageTest 11 233472 block_233472_11 block_235520_11

private theorem block_237568_12 : checkPow stageTest 237568 12 = true :=
  checkPow_join stageTest 11 237568 block_237568_11 block_239616_11

private theorem block_241664_12 : checkPow stageTest 241664 12 = true :=
  checkPow_join stageTest 11 241664 block_241664_11 block_243712_11

private theorem block_245760_12 : checkPow stageTest 245760 12 = true :=
  checkPow_join stageTest 11 245760 block_245760_11 block_247808_11

private theorem block_249856_12 : checkPow stageTest 249856 12 = true :=
  checkPow_join stageTest 11 249856 block_249856_11 block_251904_11

private theorem block_253952_12 : checkPow stageTest 253952 12 = true :=
  checkPow_join stageTest 11 253952 block_253952_11 block_256000_11

private theorem block_258048_12 : checkPow stageTest 258048 12 = true :=
  checkPow_join stageTest 11 258048 block_258048_11 block_260096_11

private theorem block_0_13 : checkPow stageTest 0 13 = true :=
  checkPow_join stageTest 12 0 block_0_12 block_4096_12

private theorem block_8192_13 : checkPow stageTest 8192 13 = true :=
  checkPow_join stageTest 12 8192 block_8192_12 block_12288_12

private theorem block_16384_13 : checkPow stageTest 16384 13 = true :=
  checkPow_join stageTest 12 16384 block_16384_12 block_20480_12

private theorem block_24576_13 : checkPow stageTest 24576 13 = true :=
  checkPow_join stageTest 12 24576 block_24576_12 block_28672_12

private theorem block_32768_13 : checkPow stageTest 32768 13 = true :=
  checkPow_join stageTest 12 32768 block_32768_12 block_36864_12

private theorem block_40960_13 : checkPow stageTest 40960 13 = true :=
  checkPow_join stageTest 12 40960 block_40960_12 block_45056_12

private theorem block_49152_13 : checkPow stageTest 49152 13 = true :=
  checkPow_join stageTest 12 49152 block_49152_12 block_53248_12

private theorem block_57344_13 : checkPow stageTest 57344 13 = true :=
  checkPow_join stageTest 12 57344 block_57344_12 block_61440_12

private theorem block_65536_13 : checkPow stageTest 65536 13 = true :=
  checkPow_join stageTest 12 65536 block_65536_12 block_69632_12

private theorem block_73728_13 : checkPow stageTest 73728 13 = true :=
  checkPow_join stageTest 12 73728 block_73728_12 block_77824_12

private theorem block_81920_13 : checkPow stageTest 81920 13 = true :=
  checkPow_join stageTest 12 81920 block_81920_12 block_86016_12

private theorem block_90112_13 : checkPow stageTest 90112 13 = true :=
  checkPow_join stageTest 12 90112 block_90112_12 block_94208_12

private theorem block_98304_13 : checkPow stageTest 98304 13 = true :=
  checkPow_join stageTest 12 98304 block_98304_12 block_102400_12

private theorem block_106496_13 : checkPow stageTest 106496 13 = true :=
  checkPow_join stageTest 12 106496 block_106496_12 block_110592_12

private theorem block_114688_13 : checkPow stageTest 114688 13 = true :=
  checkPow_join stageTest 12 114688 block_114688_12 block_118784_12

private theorem block_122880_13 : checkPow stageTest 122880 13 = true :=
  checkPow_join stageTest 12 122880 block_122880_12 block_126976_12

private theorem block_131072_13 : checkPow stageTest 131072 13 = true :=
  checkPow_join stageTest 12 131072 block_131072_12 block_135168_12

private theorem block_139264_13 : checkPow stageTest 139264 13 = true :=
  checkPow_join stageTest 12 139264 block_139264_12 block_143360_12

private theorem block_147456_13 : checkPow stageTest 147456 13 = true :=
  checkPow_join stageTest 12 147456 block_147456_12 block_151552_12

private theorem block_155648_13 : checkPow stageTest 155648 13 = true :=
  checkPow_join stageTest 12 155648 block_155648_12 block_159744_12

private theorem block_163840_13 : checkPow stageTest 163840 13 = true :=
  checkPow_join stageTest 12 163840 block_163840_12 block_167936_12

private theorem block_172032_13 : checkPow stageTest 172032 13 = true :=
  checkPow_join stageTest 12 172032 block_172032_12 block_176128_12

private theorem block_180224_13 : checkPow stageTest 180224 13 = true :=
  checkPow_join stageTest 12 180224 block_180224_12 block_184320_12

private theorem block_188416_13 : checkPow stageTest 188416 13 = true :=
  checkPow_join stageTest 12 188416 block_188416_12 block_192512_12

private theorem block_196608_13 : checkPow stageTest 196608 13 = true :=
  checkPow_join stageTest 12 196608 block_196608_12 block_200704_12

private theorem block_204800_13 : checkPow stageTest 204800 13 = true :=
  checkPow_join stageTest 12 204800 block_204800_12 block_208896_12

private theorem block_212992_13 : checkPow stageTest 212992 13 = true :=
  checkPow_join stageTest 12 212992 block_212992_12 block_217088_12

private theorem block_221184_13 : checkPow stageTest 221184 13 = true :=
  checkPow_join stageTest 12 221184 block_221184_12 block_225280_12

private theorem block_229376_13 : checkPow stageTest 229376 13 = true :=
  checkPow_join stageTest 12 229376 block_229376_12 block_233472_12

private theorem block_237568_13 : checkPow stageTest 237568 13 = true :=
  checkPow_join stageTest 12 237568 block_237568_12 block_241664_12

private theorem block_245760_13 : checkPow stageTest 245760 13 = true :=
  checkPow_join stageTest 12 245760 block_245760_12 block_249856_12

private theorem block_253952_13 : checkPow stageTest 253952 13 = true :=
  checkPow_join stageTest 12 253952 block_253952_12 block_258048_12

private theorem block_0_14 : checkPow stageTest 0 14 = true :=
  checkPow_join stageTest 13 0 block_0_13 block_8192_13

private theorem block_16384_14 : checkPow stageTest 16384 14 = true :=
  checkPow_join stageTest 13 16384 block_16384_13 block_24576_13

private theorem block_32768_14 : checkPow stageTest 32768 14 = true :=
  checkPow_join stageTest 13 32768 block_32768_13 block_40960_13

private theorem block_49152_14 : checkPow stageTest 49152 14 = true :=
  checkPow_join stageTest 13 49152 block_49152_13 block_57344_13

private theorem block_65536_14 : checkPow stageTest 65536 14 = true :=
  checkPow_join stageTest 13 65536 block_65536_13 block_73728_13

private theorem block_81920_14 : checkPow stageTest 81920 14 = true :=
  checkPow_join stageTest 13 81920 block_81920_13 block_90112_13

private theorem block_98304_14 : checkPow stageTest 98304 14 = true :=
  checkPow_join stageTest 13 98304 block_98304_13 block_106496_13

private theorem block_114688_14 : checkPow stageTest 114688 14 = true :=
  checkPow_join stageTest 13 114688 block_114688_13 block_122880_13

private theorem block_131072_14 : checkPow stageTest 131072 14 = true :=
  checkPow_join stageTest 13 131072 block_131072_13 block_139264_13

private theorem block_147456_14 : checkPow stageTest 147456 14 = true :=
  checkPow_join stageTest 13 147456 block_147456_13 block_155648_13

private theorem block_163840_14 : checkPow stageTest 163840 14 = true :=
  checkPow_join stageTest 13 163840 block_163840_13 block_172032_13

private theorem block_180224_14 : checkPow stageTest 180224 14 = true :=
  checkPow_join stageTest 13 180224 block_180224_13 block_188416_13

private theorem block_196608_14 : checkPow stageTest 196608 14 = true :=
  checkPow_join stageTest 13 196608 block_196608_13 block_204800_13

private theorem block_212992_14 : checkPow stageTest 212992 14 = true :=
  checkPow_join stageTest 13 212992 block_212992_13 block_221184_13

private theorem block_229376_14 : checkPow stageTest 229376 14 = true :=
  checkPow_join stageTest 13 229376 block_229376_13 block_237568_13

private theorem block_245760_14 : checkPow stageTest 245760 14 = true :=
  checkPow_join stageTest 13 245760 block_245760_13 block_253952_13

private theorem block_0_15 : checkPow stageTest 0 15 = true :=
  checkPow_join stageTest 14 0 block_0_14 block_16384_14

private theorem block_32768_15 : checkPow stageTest 32768 15 = true :=
  checkPow_join stageTest 14 32768 block_32768_14 block_49152_14

private theorem block_65536_15 : checkPow stageTest 65536 15 = true :=
  checkPow_join stageTest 14 65536 block_65536_14 block_81920_14

private theorem block_98304_15 : checkPow stageTest 98304 15 = true :=
  checkPow_join stageTest 14 98304 block_98304_14 block_114688_14

private theorem block_131072_15 : checkPow stageTest 131072 15 = true :=
  checkPow_join stageTest 14 131072 block_131072_14 block_147456_14

private theorem block_163840_15 : checkPow stageTest 163840 15 = true :=
  checkPow_join stageTest 14 163840 block_163840_14 block_180224_14

private theorem block_196608_15 : checkPow stageTest 196608 15 = true :=
  checkPow_join stageTest 14 196608 block_196608_14 block_212992_14

private theorem block_229376_15 : checkPow stageTest 229376 15 = true :=
  checkPow_join stageTest 14 229376 block_229376_14 block_245760_14

private theorem block_0_16 : checkPow stageTest 0 16 = true :=
  checkPow_join stageTest 15 0 block_0_15 block_32768_15

private theorem block_65536_16 : checkPow stageTest 65536 16 = true :=
  checkPow_join stageTest 15 65536 block_65536_15 block_98304_15

private theorem block_131072_16 : checkPow stageTest 131072 16 = true :=
  checkPow_join stageTest 15 131072 block_131072_15 block_163840_15

private theorem block_196608_16 : checkPow stageTest 196608 16 = true :=
  checkPow_join stageTest 15 196608 block_196608_15 block_229376_15

private theorem block_0_17 : checkPow stageTest 0 17 = true :=
  checkPow_join stageTest 16 0 block_0_16 block_65536_16

private theorem block_131072_17 : checkPow stageTest 131072 17 = true :=
  checkPow_join stageTest 16 131072 block_131072_16 block_196608_16

private theorem block_0_18 : checkPow stageTest 0 18 = true :=
  checkPow_join stageTest 17 0 block_0_17 block_131072_17

private theorem block_262144_11 : checkPow stageTest 262144 11 = true :=
  checkPow_join stageTest 10 262144 block_262144_10 block_263168_10

private theorem block_264192_11 : checkPow stageTest 264192 11 = true :=
  checkPow_join stageTest 10 264192 block_264192_10 block_265216_10

private theorem block_266240_11 : checkPow stageTest 266240 11 = true :=
  checkPow_join stageTest 10 266240 block_266240_10 block_267264_10

private theorem block_268288_11 : checkPow stageTest 268288 11 = true :=
  checkPow_join stageTest 10 268288 block_268288_10 block_269312_10

private theorem block_270336_11 : checkPow stageTest 270336 11 = true :=
  checkPow_join stageTest 10 270336 block_270336_10 block_271360_10

private theorem block_272384_11 : checkPow stageTest 272384 11 = true :=
  checkPow_join stageTest 10 272384 block_272384_10 block_273408_10

private theorem block_274432_11 : checkPow stageTest 274432 11 = true :=
  checkPow_join stageTest 10 274432 block_274432_10 block_275456_10

private theorem block_276480_11 : checkPow stageTest 276480 11 = true :=
  checkPow_join stageTest 10 276480 block_276480_10 block_277504_10

private theorem block_278528_11 : checkPow stageTest 278528 11 = true :=
  checkPow_join stageTest 10 278528 block_278528_10 block_279552_10

private theorem block_280576_11 : checkPow stageTest 280576 11 = true :=
  checkPow_join stageTest 10 280576 block_280576_10 block_281600_10

private theorem block_282624_11 : checkPow stageTest 282624 11 = true :=
  checkPow_join stageTest 10 282624 block_282624_10 block_283648_10

private theorem block_284672_11 : checkPow stageTest 284672 11 = true :=
  checkPow_join stageTest 10 284672 block_284672_10 block_285696_10

private theorem block_286720_11 : checkPow stageTest 286720 11 = true :=
  checkPow_join stageTest 10 286720 block_286720_10 block_287744_10

private theorem block_288768_11 : checkPow stageTest 288768 11 = true :=
  checkPow_join stageTest 10 288768 block_288768_10 block_289792_10

private theorem block_290816_11 : checkPow stageTest 290816 11 = true :=
  checkPow_join stageTest 10 290816 block_290816_10 block_291840_10

private theorem block_292864_11 : checkPow stageTest 292864 11 = true :=
  checkPow_join stageTest 10 292864 block_292864_10 block_293888_10

private theorem block_262144_12 : checkPow stageTest 262144 12 = true :=
  checkPow_join stageTest 11 262144 block_262144_11 block_264192_11

private theorem block_266240_12 : checkPow stageTest 266240 12 = true :=
  checkPow_join stageTest 11 266240 block_266240_11 block_268288_11

private theorem block_270336_12 : checkPow stageTest 270336 12 = true :=
  checkPow_join stageTest 11 270336 block_270336_11 block_272384_11

private theorem block_274432_12 : checkPow stageTest 274432 12 = true :=
  checkPow_join stageTest 11 274432 block_274432_11 block_276480_11

private theorem block_278528_12 : checkPow stageTest 278528 12 = true :=
  checkPow_join stageTest 11 278528 block_278528_11 block_280576_11

private theorem block_282624_12 : checkPow stageTest 282624 12 = true :=
  checkPow_join stageTest 11 282624 block_282624_11 block_284672_11

private theorem block_286720_12 : checkPow stageTest 286720 12 = true :=
  checkPow_join stageTest 11 286720 block_286720_11 block_288768_11

private theorem block_290816_12 : checkPow stageTest 290816 12 = true :=
  checkPow_join stageTest 11 290816 block_290816_11 block_292864_11

private theorem block_262144_13 : checkPow stageTest 262144 13 = true :=
  checkPow_join stageTest 12 262144 block_262144_12 block_266240_12

private theorem block_270336_13 : checkPow stageTest 270336 13 = true :=
  checkPow_join stageTest 12 270336 block_270336_12 block_274432_12

private theorem block_278528_13 : checkPow stageTest 278528 13 = true :=
  checkPow_join stageTest 12 278528 block_278528_12 block_282624_12

private theorem block_286720_13 : checkPow stageTest 286720 13 = true :=
  checkPow_join stageTest 12 286720 block_286720_12 block_290816_12

private theorem block_262144_14 : checkPow stageTest 262144 14 = true :=
  checkPow_join stageTest 13 262144 block_262144_13 block_270336_13

private theorem block_278528_14 : checkPow stageTest 278528 14 = true :=
  checkPow_join stageTest 13 278528 block_278528_13 block_286720_13

private theorem block_262144_15 : checkPow stageTest 262144 15 = true :=
  checkPow_join stageTest 14 262144 block_262144_14 block_278528_14

private theorem block_294912_11 : checkPow stageTest 294912 11 = true :=
  checkPow_join stageTest 10 294912 block_294912_10 block_295936_10

private theorem block_296960_11 : checkPow stageTest 296960 11 = true :=
  checkPow_join stageTest 10 296960 block_296960_10 block_297984_10

private theorem block_299008_11 : checkPow stageTest 299008 11 = true :=
  checkPow_join stageTest 10 299008 block_299008_10 block_300032_10

private theorem block_301056_11 : checkPow stageTest 301056 11 = true :=
  checkPow_join stageTest 10 301056 block_301056_10 block_302080_10

private theorem block_294912_12 : checkPow stageTest 294912 12 = true :=
  checkPow_join stageTest 11 294912 block_294912_11 block_296960_11

private theorem block_299008_12 : checkPow stageTest 299008 12 = true :=
  checkPow_join stageTest 11 299008 block_299008_11 block_301056_11

private theorem block_294912_13 : checkPow stageTest 294912 13 = true :=
  checkPow_join stageTest 12 294912 block_294912_12 block_299008_12

private theorem block_303104_11 : checkPow stageTest 303104 11 = true :=
  checkPow_join stageTest 10 303104 block_303104_10 block_304128_10

private theorem block_305152_11 : checkPow stageTest 305152 11 = true :=
  checkPow_join stageTest 10 305152 block_305152_10 block_306176_10

private theorem block_303104_12 : checkPow stageTest 303104 12 = true :=
  checkPow_join stageTest 11 303104 block_303104_11 block_305152_11

/-- Every stage identity has been checked on every ambient point. -/
public theorem stages_checked (i : Fin 306936) : stageTest i.val = true :=
  FirstFourModel.covered_checks stageTest
    block_0_18 block_262144_15 block_294912_13 block_303104_12 i

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.NumericalChecks
