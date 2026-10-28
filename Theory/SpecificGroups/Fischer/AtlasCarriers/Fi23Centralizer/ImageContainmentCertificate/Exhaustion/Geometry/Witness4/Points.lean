module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness4.Data

/-!
# Witness 4: commutation and the fixed complement

The unchanged saved inverse cycles are compared with proposed packed actions.
Every equality and support assertion is checked by the Lean kernel.
Source: `ImageContainmentCertificate/source/centralizer-data.g`, for
GLS3 Table 5.3u. Reproduction and license are recorded in `Geometry/source/`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry.Witness4
open Sporadic.Fischer.AtlasCarriers
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
open Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck
open Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
set_option Elab.async false

private theorem point0 : checkRange (checkAt (WitnessCheck action supportMask)) 7 0 = true := by decide +kernel

private theorem point1 : checkRange (checkAt (WitnessCheck action supportMask)) 7 128 = true := by decide +kernel

private theorem point2 : checkRange (checkAt (WitnessCheck action supportMask)) 7 256 = true := by decide +kernel

private theorem point3 : checkRange (checkAt (WitnessCheck action supportMask)) 7 384 = true := by decide +kernel

private theorem point4 : checkRange (checkAt (WitnessCheck action supportMask)) 7 512 = true := by decide +kernel

private theorem point5 : checkRange (checkAt (WitnessCheck action supportMask)) 7 640 = true := by decide +kernel

private theorem point6 : checkRange (checkAt (WitnessCheck action supportMask)) 7 768 = true := by decide +kernel

private theorem point7 : checkRange (checkAt (WitnessCheck action supportMask)) 7 896 = true := by decide +kernel

private theorem point8 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1024 = true := by decide +kernel

private theorem point9 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1152 = true := by decide +kernel

private theorem point10 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1280 = true := by decide +kernel

private theorem point11 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1408 = true := by decide +kernel

private theorem point12 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1536 = true := by decide +kernel

private theorem point13 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1664 = true := by decide +kernel

private theorem point14 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1792 = true := by decide +kernel

private theorem point15 : checkRange (checkAt (WitnessCheck action supportMask)) 7 1920 = true := by decide +kernel

private theorem point16 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2048 = true := by decide +kernel

private theorem point17 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2176 = true := by decide +kernel

private theorem point18 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2304 = true := by decide +kernel

private theorem point19 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2432 = true := by decide +kernel

private theorem point20 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2560 = true := by decide +kernel

private theorem point21 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2688 = true := by decide +kernel

private theorem point22 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2816 = true := by decide +kernel

private theorem point23 : checkRange (checkAt (WitnessCheck action supportMask)) 7 2944 = true := by decide +kernel

private theorem point24 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3072 = true := by decide +kernel

private theorem point25 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3200 = true := by decide +kernel

private theorem point26 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3328 = true := by decide +kernel

private theorem point27 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3456 = true := by decide +kernel

private theorem point28 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3584 = true := by decide +kernel

private theorem point29 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3712 = true := by decide +kernel

private theorem point30 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3840 = true := by decide +kernel

private theorem point31 : checkRange (checkAt (WitnessCheck action supportMask)) 7 3968 = true := by decide +kernel

private theorem point32 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4096 = true := by decide +kernel

private theorem point33 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4224 = true := by decide +kernel

private theorem point34 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4352 = true := by decide +kernel

private theorem point35 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4480 = true := by decide +kernel

private theorem point36 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4608 = true := by decide +kernel

private theorem point37 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4736 = true := by decide +kernel

private theorem point38 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4864 = true := by decide +kernel

private theorem point39 : checkRange (checkAt (WitnessCheck action supportMask)) 7 4992 = true := by decide +kernel

private theorem point40 : checkRange (checkAt (WitnessCheck action supportMask)) 7 5120 = true := by decide +kernel

private theorem point41 : checkRange (checkAt (WitnessCheck action supportMask)) 7 5248 = true := by decide +kernel

private theorem point42 : checkRange (checkAt (WitnessCheck action supportMask)) 7 5376 = true := by decide +kernel

private theorem point43 : checkRange (checkAt (WitnessCheck action supportMask)) 7 5504 = true := by decide +kernel

private theorem point44 : checkRange (checkAt (WitnessCheck action supportMask)) 7 5632 = true := by decide +kernel

private theorem point45 : checkRange (checkAt (WitnessCheck action supportMask)) 7 5760 = true := by decide +kernel

private theorem point46 : checkRange (checkAt (WitnessCheck action supportMask)) 7 5888 = true := by decide +kernel

private theorem point47 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6016 = true := by decide +kernel

private theorem point48 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6144 = true := by decide +kernel

private theorem point49 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6272 = true := by decide +kernel

private theorem point50 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6400 = true := by decide +kernel

private theorem point51 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6528 = true := by decide +kernel

private theorem point52 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6656 = true := by decide +kernel

private theorem point53 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6784 = true := by decide +kernel

private theorem point54 : checkRange (checkAt (WitnessCheck action supportMask)) 7 6912 = true := by decide +kernel

private theorem point55 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7040 = true := by decide +kernel

private theorem point56 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7168 = true := by decide +kernel

private theorem point57 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7296 = true := by decide +kernel

private theorem point58 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7424 = true := by decide +kernel

private theorem point59 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7552 = true := by decide +kernel

private theorem point60 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7680 = true := by decide +kernel

private theorem point61 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7808 = true := by decide +kernel

private theorem point62 : checkRange (checkAt (WitnessCheck action supportMask)) 7 7936 = true := by decide +kernel

private theorem point63 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8064 = true := by decide +kernel

private theorem point64 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8192 = true := by decide +kernel

private theorem point65 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8320 = true := by decide +kernel

private theorem point66 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8448 = true := by decide +kernel

private theorem point67 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8576 = true := by decide +kernel

private theorem point68 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8704 = true := by decide +kernel

private theorem point69 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8832 = true := by decide +kernel

private theorem point70 : checkRange (checkAt (WitnessCheck action supportMask)) 7 8960 = true := by decide +kernel

private theorem point71 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9088 = true := by decide +kernel

private theorem point72 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9216 = true := by decide +kernel

private theorem point73 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9344 = true := by decide +kernel

private theorem point74 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9472 = true := by decide +kernel

private theorem point75 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9600 = true := by decide +kernel

private theorem point76 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9728 = true := by decide +kernel

private theorem point77 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9856 = true := by decide +kernel

private theorem point78 : checkRange (checkAt (WitnessCheck action supportMask)) 7 9984 = true := by decide +kernel

private theorem point79 : checkRange (checkAt (WitnessCheck action supportMask)) 7 10112 = true := by decide +kernel

private theorem point80 : checkRange (checkAt (WitnessCheck action supportMask)) 7 10240 = true := by decide +kernel

private theorem point81 : checkRange (checkAt (WitnessCheck action supportMask)) 7 10368 = true := by decide +kernel

private theorem point82 : checkRange (checkAt (WitnessCheck action supportMask)) 7 10496 = true := by decide +kernel

private theorem point83 : checkRange (checkAt (WitnessCheck action supportMask)) 7 10624 = true := by decide +kernel

private theorem point84 : checkRange (checkAt (WitnessCheck action supportMask)) 7 10752 = true := by decide +kernel

private theorem point85 : checkRange (checkAt (WitnessCheck action supportMask)) 7 10880 = true := by decide +kernel

private theorem point86 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11008 = true := by decide +kernel

private theorem point87 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11136 = true := by decide +kernel

private theorem point88 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11264 = true := by decide +kernel

private theorem point89 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11392 = true := by decide +kernel

private theorem point90 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11520 = true := by decide +kernel

private theorem point91 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11648 = true := by decide +kernel

private theorem point92 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11776 = true := by decide +kernel

private theorem point93 : checkRange (checkAt (WitnessCheck action supportMask)) 7 11904 = true := by decide +kernel

private theorem point94 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12032 = true := by decide +kernel

private theorem point95 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12160 = true := by decide +kernel

private theorem point96 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12288 = true := by decide +kernel

private theorem point97 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12416 = true := by decide +kernel

private theorem point98 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12544 = true := by decide +kernel

private theorem point99 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12672 = true := by decide +kernel

private theorem point100 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12800 = true := by decide +kernel

private theorem point101 : checkRange (checkAt (WitnessCheck action supportMask)) 7 12928 = true := by decide +kernel

private theorem point102 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13056 = true := by decide +kernel

private theorem point103 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13184 = true := by decide +kernel

private theorem point104 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13312 = true := by decide +kernel

private theorem point105 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13440 = true := by decide +kernel

private theorem point106 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13568 = true := by decide +kernel

private theorem point107 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13696 = true := by decide +kernel

private theorem point108 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13824 = true := by decide +kernel

private theorem point109 : checkRange (checkAt (WitnessCheck action supportMask)) 7 13952 = true := by decide +kernel

private theorem point110 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14080 = true := by decide +kernel

private theorem point111 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14208 = true := by decide +kernel

private theorem point112 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14336 = true := by decide +kernel

private theorem point113 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14464 = true := by decide +kernel

private theorem point114 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14592 = true := by decide +kernel

private theorem point115 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14720 = true := by decide +kernel

private theorem point116 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14848 = true := by decide +kernel

private theorem point117 : checkRange (checkAt (WitnessCheck action supportMask)) 7 14976 = true := by decide +kernel

private theorem point118 : checkRange (checkAt (WitnessCheck action supportMask)) 7 15104 = true := by decide +kernel

private theorem point119 : checkRange (checkAt (WitnessCheck action supportMask)) 7 15232 = true := by decide +kernel

private theorem point120 : checkRange (checkAt (WitnessCheck action supportMask)) 7 15360 = true := by decide +kernel

private theorem point121 : checkRange (checkAt (WitnessCheck action supportMask)) 7 15488 = true := by decide +kernel

private theorem point122 : checkRange (checkAt (WitnessCheck action supportMask)) 7 15616 = true := by decide +kernel

private theorem point123 : checkRange (checkAt (WitnessCheck action supportMask)) 7 15744 = true := by decide +kernel

private theorem point124 : checkRange (checkAt (WitnessCheck action supportMask)) 7 15872 = true := by decide +kernel

private theorem point125 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16000 = true := by decide +kernel

private theorem point126 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16128 = true := by decide +kernel

private theorem point127 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16256 = true := by decide +kernel

private theorem point128 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16384 = true := by decide +kernel

private theorem point129 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16512 = true := by decide +kernel

private theorem point130 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16640 = true := by decide +kernel

private theorem point131 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16768 = true := by decide +kernel

private theorem point132 : checkRange (checkAt (WitnessCheck action supportMask)) 7 16896 = true := by decide +kernel

private theorem point133 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17024 = true := by decide +kernel

private theorem point134 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17152 = true := by decide +kernel

private theorem point135 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17280 = true := by decide +kernel

private theorem point136 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17408 = true := by decide +kernel

private theorem point137 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17536 = true := by decide +kernel

private theorem point138 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17664 = true := by decide +kernel

private theorem point139 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17792 = true := by decide +kernel

private theorem point140 : checkRange (checkAt (WitnessCheck action supportMask)) 7 17920 = true := by decide +kernel

private theorem point141 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18048 = true := by decide +kernel

private theorem point142 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18176 = true := by decide +kernel

private theorem point143 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18304 = true := by decide +kernel

private theorem point144 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18432 = true := by decide +kernel

private theorem point145 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18560 = true := by decide +kernel

private theorem point146 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18688 = true := by decide +kernel

private theorem point147 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18816 = true := by decide +kernel

private theorem point148 : checkRange (checkAt (WitnessCheck action supportMask)) 7 18944 = true := by decide +kernel

private theorem point149 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19072 = true := by decide +kernel

private theorem point150 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19200 = true := by decide +kernel

private theorem point151 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19328 = true := by decide +kernel

private theorem point152 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19456 = true := by decide +kernel

private theorem point153 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19584 = true := by decide +kernel

private theorem point154 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19712 = true := by decide +kernel

private theorem point155 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19840 = true := by decide +kernel

private theorem point156 : checkRange (checkAt (WitnessCheck action supportMask)) 7 19968 = true := by decide +kernel

private theorem point157 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20096 = true := by decide +kernel

private theorem point158 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20224 = true := by decide +kernel

private theorem point159 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20352 = true := by decide +kernel

private theorem point160 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20480 = true := by decide +kernel

private theorem point161 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20608 = true := by decide +kernel

private theorem point162 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20736 = true := by decide +kernel

private theorem point163 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20864 = true := by decide +kernel

private theorem point164 : checkRange (checkAt (WitnessCheck action supportMask)) 7 20992 = true := by decide +kernel

private theorem point165 : checkRange (checkAt (WitnessCheck action supportMask)) 7 21120 = true := by decide +kernel

private theorem point166 : checkRange (checkAt (WitnessCheck action supportMask)) 7 21248 = true := by decide +kernel

private theorem point167 : checkRange (checkAt (WitnessCheck action supportMask)) 7 21376 = true := by decide +kernel

private theorem point168 : checkRange (checkAt (WitnessCheck action supportMask)) 7 21504 = true := by decide +kernel

private theorem point169 : checkRange (checkAt (WitnessCheck action supportMask)) 7 21632 = true := by decide +kernel

private theorem point170 : checkRange (checkAt (WitnessCheck action supportMask)) 7 21760 = true := by decide +kernel

private theorem point171 : checkRange (checkAt (WitnessCheck action supportMask)) 7 21888 = true := by decide +kernel

private theorem point172 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22016 = true := by decide +kernel

private theorem point173 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22144 = true := by decide +kernel

private theorem point174 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22272 = true := by decide +kernel

private theorem point175 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22400 = true := by decide +kernel

private theorem point176 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22528 = true := by decide +kernel

private theorem point177 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22656 = true := by decide +kernel

private theorem point178 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22784 = true := by decide +kernel

private theorem point179 : checkRange (checkAt (WitnessCheck action supportMask)) 7 22912 = true := by decide +kernel

private theorem point180 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23040 = true := by decide +kernel

private theorem point181 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23168 = true := by decide +kernel

private theorem point182 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23296 = true := by decide +kernel

private theorem point183 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23424 = true := by decide +kernel

private theorem point184 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23552 = true := by decide +kernel

private theorem point185 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23680 = true := by decide +kernel

private theorem point186 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23808 = true := by decide +kernel

private theorem point187 : checkRange (checkAt (WitnessCheck action supportMask)) 7 23936 = true := by decide +kernel

private theorem point188 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24064 = true := by decide +kernel

private theorem point189 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24192 = true := by decide +kernel

private theorem point190 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24320 = true := by decide +kernel

private theorem point191 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24448 = true := by decide +kernel

private theorem point192 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24576 = true := by decide +kernel

private theorem point193 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24704 = true := by decide +kernel

private theorem point194 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24832 = true := by decide +kernel

private theorem point195 : checkRange (checkAt (WitnessCheck action supportMask)) 7 24960 = true := by decide +kernel

private theorem point196 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25088 = true := by decide +kernel

private theorem point197 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25216 = true := by decide +kernel

private theorem point198 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25344 = true := by decide +kernel

private theorem point199 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25472 = true := by decide +kernel

private theorem point200 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25600 = true := by decide +kernel

private theorem point201 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25728 = true := by decide +kernel

private theorem point202 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25856 = true := by decide +kernel

private theorem point203 : checkRange (checkAt (WitnessCheck action supportMask)) 7 25984 = true := by decide +kernel

private theorem point204 : checkRange (checkAt (WitnessCheck action supportMask)) 7 26112 = true := by decide +kernel

private theorem point205 : checkRange (checkAt (WitnessCheck action supportMask)) 7 26240 = true := by decide +kernel

private theorem point206 : checkRange (checkAt (WitnessCheck action supportMask)) 7 26368 = true := by decide +kernel

private theorem point207 : checkRange (checkAt (WitnessCheck action supportMask)) 7 26496 = true := by decide +kernel

private theorem point208 : checkRange (checkAt (WitnessCheck action supportMask)) 7 26624 = true := by decide +kernel

private theorem point209 : checkRange (checkAt (WitnessCheck action supportMask)) 7 26752 = true := by decide +kernel

private theorem point210 : checkRange (checkAt (WitnessCheck action supportMask)) 7 26880 = true := by decide +kernel

private theorem point211 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27008 = true := by decide +kernel

private theorem point212 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27136 = true := by decide +kernel

private theorem point213 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27264 = true := by decide +kernel

private theorem point214 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27392 = true := by decide +kernel

private theorem point215 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27520 = true := by decide +kernel

private theorem point216 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27648 = true := by decide +kernel

private theorem point217 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27776 = true := by decide +kernel

private theorem point218 : checkRange (checkAt (WitnessCheck action supportMask)) 7 27904 = true := by decide +kernel

private theorem point219 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28032 = true := by decide +kernel

private theorem point220 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28160 = true := by decide +kernel

private theorem point221 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28288 = true := by decide +kernel

private theorem point222 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28416 = true := by decide +kernel

private theorem point223 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28544 = true := by decide +kernel

private theorem point224 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28672 = true := by decide +kernel

private theorem point225 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28800 = true := by decide +kernel

private theorem point226 : checkRange (checkAt (WitnessCheck action supportMask)) 7 28928 = true := by decide +kernel

private theorem point227 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29056 = true := by decide +kernel

private theorem point228 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29184 = true := by decide +kernel

private theorem point229 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29312 = true := by decide +kernel

private theorem point230 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29440 = true := by decide +kernel

private theorem point231 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29568 = true := by decide +kernel

private theorem point232 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29696 = true := by decide +kernel

private theorem point233 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29824 = true := by decide +kernel

private theorem point234 : checkRange (checkAt (WitnessCheck action supportMask)) 7 29952 = true := by decide +kernel

private theorem point235 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30080 = true := by decide +kernel

private theorem point236 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30208 = true := by decide +kernel

private theorem point237 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30336 = true := by decide +kernel

private theorem point238 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30464 = true := by decide +kernel

private theorem point239 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30592 = true := by decide +kernel

private theorem point240 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30720 = true := by decide +kernel

private theorem point241 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30848 = true := by decide +kernel

private theorem point242 : checkRange (checkAt (WitnessCheck action supportMask)) 7 30976 = true := by decide +kernel

private theorem point243 : checkRange (checkAt (WitnessCheck action supportMask)) 7 31104 = true := by decide +kernel

private theorem point244 : checkRange (checkAt (WitnessCheck action supportMask)) 7 31232 = true := by decide +kernel

private theorem point245 : checkRange (checkAt (WitnessCheck action supportMask)) 7 31360 = true := by decide +kernel

private theorem point246 : checkRange (checkAt (WitnessCheck action supportMask)) 7 31488 = true := by decide +kernel

private theorem point247 : checkRange (checkAt (WitnessCheck action supportMask)) 7 31616 = true := by decide +kernel

private theorem pointBlocks (b : Fin 248) :
    checkRange (checkAt (WitnessCheck action supportMask)) 7 (2^7 * b.val) = true := by
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact point0
  · exact point1
  · exact point2
  · exact point3
  · exact point4
  · exact point5
  · exact point6
  · exact point7
  · exact point8
  · exact point9
  · exact point10
  · exact point11
  · exact point12
  · exact point13
  · exact point14
  · exact point15
  · exact point16
  · exact point17
  · exact point18
  · exact point19
  · exact point20
  · exact point21
  · exact point22
  · exact point23
  · exact point24
  · exact point25
  · exact point26
  · exact point27
  · exact point28
  · exact point29
  · exact point30
  · exact point31
  · exact point32
  · exact point33
  · exact point34
  · exact point35
  · exact point36
  · exact point37
  · exact point38
  · exact point39
  · exact point40
  · exact point41
  · exact point42
  · exact point43
  · exact point44
  · exact point45
  · exact point46
  · exact point47
  · exact point48
  · exact point49
  · exact point50
  · exact point51
  · exact point52
  · exact point53
  · exact point54
  · exact point55
  · exact point56
  · exact point57
  · exact point58
  · exact point59
  · exact point60
  · exact point61
  · exact point62
  · exact point63
  · exact point64
  · exact point65
  · exact point66
  · exact point67
  · exact point68
  · exact point69
  · exact point70
  · exact point71
  · exact point72
  · exact point73
  · exact point74
  · exact point75
  · exact point76
  · exact point77
  · exact point78
  · exact point79
  · exact point80
  · exact point81
  · exact point82
  · exact point83
  · exact point84
  · exact point85
  · exact point86
  · exact point87
  · exact point88
  · exact point89
  · exact point90
  · exact point91
  · exact point92
  · exact point93
  · exact point94
  · exact point95
  · exact point96
  · exact point97
  · exact point98
  · exact point99
  · exact point100
  · exact point101
  · exact point102
  · exact point103
  · exact point104
  · exact point105
  · exact point106
  · exact point107
  · exact point108
  · exact point109
  · exact point110
  · exact point111
  · exact point112
  · exact point113
  · exact point114
  · exact point115
  · exact point116
  · exact point117
  · exact point118
  · exact point119
  · exact point120
  · exact point121
  · exact point122
  · exact point123
  · exact point124
  · exact point125
  · exact point126
  · exact point127
  · exact point128
  · exact point129
  · exact point130
  · exact point131
  · exact point132
  · exact point133
  · exact point134
  · exact point135
  · exact point136
  · exact point137
  · exact point138
  · exact point139
  · exact point140
  · exact point141
  · exact point142
  · exact point143
  · exact point144
  · exact point145
  · exact point146
  · exact point147
  · exact point148
  · exact point149
  · exact point150
  · exact point151
  · exact point152
  · exact point153
  · exact point154
  · exact point155
  · exact point156
  · exact point157
  · exact point158
  · exact point159
  · exact point160
  · exact point161
  · exact point162
  · exact point163
  · exact point164
  · exact point165
  · exact point166
  · exact point167
  · exact point168
  · exact point169
  · exact point170
  · exact point171
  · exact point172
  · exact point173
  · exact point174
  · exact point175
  · exact point176
  · exact point177
  · exact point178
  · exact point179
  · exact point180
  · exact point181
  · exact point182
  · exact point183
  · exact point184
  · exact point185
  · exact point186
  · exact point187
  · exact point188
  · exact point189
  · exact point190
  · exact point191
  · exact point192
  · exact point193
  · exact point194
  · exact point195
  · exact point196
  · exact point197
  · exact point198
  · exact point199
  · exact point200
  · exact point201
  · exact point202
  · exact point203
  · exact point204
  · exact point205
  · exact point206
  · exact point207
  · exact point208
  · exact point209
  · exact point210
  · exact point211
  · exact point212
  · exact point213
  · exact point214
  · exact point215
  · exact point216
  · exact point217
  · exact point218
  · exact point219
  · exact point220
  · exact point221
  · exact point222
  · exact point223
  · exact point224
  · exact point225
  · exact point226
  · exact point227
  · exact point228
  · exact point229
  · exact point230
  · exact point231
  · exact point232
  · exact point233
  · exact point234
  · exact point235
  · exact point236
  · exact point237
  · exact point238
  · exact point239
  · exact point240
  · exact point241
  · exact point242
  · exact point243
  · exact point244
  · exact point245
  · exact point246
  · exact point247

theorem pointChecks (x : Fin 31671) : WitnessCheck action supportMask x :=
  of_check_blocks (WitnessCheck action supportMask) (by decide : 31671 ≤ 2^7 * 248) pointBlocks x

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry.Witness4
