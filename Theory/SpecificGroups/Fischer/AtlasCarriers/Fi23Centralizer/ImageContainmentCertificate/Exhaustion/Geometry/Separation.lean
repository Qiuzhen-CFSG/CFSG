module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Checking

/-!
# Kernel-checked two-point representative recurrence

Each block checks 128 original labels, including both proposed images,
strictly shorter parent codes, and the separating inequality. Induction in
`Checking` transports these constant-size checks to the original words.
Source: ATLAS F23G1-p31671B0, for GLS3 Table 5.3u.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry
open GeneratorLiftCertificate
set_option Elab.async false

private theorem block0 : checkRange (checkAt EvaluationCheck) 7 0 = true := by decide +kernel

private theorem block1 : checkRange (checkAt EvaluationCheck) 7 128 = true := by decide +kernel

private theorem block2 : checkRange (checkAt EvaluationCheck) 7 256 = true := by decide +kernel

private theorem block3 : checkRange (checkAt EvaluationCheck) 7 384 = true := by decide +kernel

private theorem block4 : checkRange (checkAt EvaluationCheck) 7 512 = true := by decide +kernel

private theorem block5 : checkRange (checkAt EvaluationCheck) 7 640 = true := by decide +kernel

private theorem block6 : checkRange (checkAt EvaluationCheck) 7 768 = true := by decide +kernel

private theorem block7 : checkRange (checkAt EvaluationCheck) 7 896 = true := by decide +kernel

private theorem block8 : checkRange (checkAt EvaluationCheck) 7 1024 = true := by decide +kernel

private theorem block9 : checkRange (checkAt EvaluationCheck) 7 1152 = true := by decide +kernel

private theorem block10 : checkRange (checkAt EvaluationCheck) 7 1280 = true := by decide +kernel

private theorem block11 : checkRange (checkAt EvaluationCheck) 7 1408 = true := by decide +kernel

private theorem block12 : checkRange (checkAt EvaluationCheck) 7 1536 = true := by decide +kernel

private theorem block13 : checkRange (checkAt EvaluationCheck) 7 1664 = true := by decide +kernel

private theorem block14 : checkRange (checkAt EvaluationCheck) 7 1792 = true := by decide +kernel

private theorem block15 : checkRange (checkAt EvaluationCheck) 7 1920 = true := by decide +kernel

private theorem block16 : checkRange (checkAt EvaluationCheck) 7 2048 = true := by decide +kernel

private theorem block17 : checkRange (checkAt EvaluationCheck) 7 2176 = true := by decide +kernel

private theorem block18 : checkRange (checkAt EvaluationCheck) 7 2304 = true := by decide +kernel

private theorem block19 : checkRange (checkAt EvaluationCheck) 7 2432 = true := by decide +kernel

private theorem block20 : checkRange (checkAt EvaluationCheck) 7 2560 = true := by decide +kernel

private theorem block21 : checkRange (checkAt EvaluationCheck) 7 2688 = true := by decide +kernel

private theorem block22 : checkRange (checkAt EvaluationCheck) 7 2816 = true := by decide +kernel

private theorem block23 : checkRange (checkAt EvaluationCheck) 7 2944 = true := by decide +kernel

private theorem block24 : checkRange (checkAt EvaluationCheck) 7 3072 = true := by decide +kernel

private theorem block25 : checkRange (checkAt EvaluationCheck) 7 3200 = true := by decide +kernel

private theorem block26 : checkRange (checkAt EvaluationCheck) 7 3328 = true := by decide +kernel

private theorem block27 : checkRange (checkAt EvaluationCheck) 7 3456 = true := by decide +kernel

private theorem block28 : checkRange (checkAt EvaluationCheck) 7 3584 = true := by decide +kernel

private theorem block29 : checkRange (checkAt EvaluationCheck) 7 3712 = true := by decide +kernel

private theorem block30 : checkRange (checkAt EvaluationCheck) 7 3840 = true := by decide +kernel

private theorem block31 : checkRange (checkAt EvaluationCheck) 7 3968 = true := by decide +kernel

private theorem block32 : checkRange (checkAt EvaluationCheck) 7 4096 = true := by decide +kernel

private theorem block33 : checkRange (checkAt EvaluationCheck) 7 4224 = true := by decide +kernel

private theorem block34 : checkRange (checkAt EvaluationCheck) 7 4352 = true := by decide +kernel

private theorem block35 : checkRange (checkAt EvaluationCheck) 7 4480 = true := by decide +kernel

private theorem block36 : checkRange (checkAt EvaluationCheck) 7 4608 = true := by decide +kernel

private theorem block37 : checkRange (checkAt EvaluationCheck) 7 4736 = true := by decide +kernel

private theorem block38 : checkRange (checkAt EvaluationCheck) 7 4864 = true := by decide +kernel

private theorem block39 : checkRange (checkAt EvaluationCheck) 7 4992 = true := by decide +kernel

private theorem block40 : checkRange (checkAt EvaluationCheck) 7 5120 = true := by decide +kernel

private theorem block41 : checkRange (checkAt EvaluationCheck) 7 5248 = true := by decide +kernel

private theorem block42 : checkRange (checkAt EvaluationCheck) 7 5376 = true := by decide +kernel

private theorem block43 : checkRange (checkAt EvaluationCheck) 7 5504 = true := by decide +kernel

private theorem block44 : checkRange (checkAt EvaluationCheck) 7 5632 = true := by decide +kernel

private theorem block45 : checkRange (checkAt EvaluationCheck) 7 5760 = true := by decide +kernel

private theorem block46 : checkRange (checkAt EvaluationCheck) 7 5888 = true := by decide +kernel

private theorem block47 : checkRange (checkAt EvaluationCheck) 7 6016 = true := by decide +kernel

private theorem block48 : checkRange (checkAt EvaluationCheck) 7 6144 = true := by decide +kernel

private theorem block49 : checkRange (checkAt EvaluationCheck) 7 6272 = true := by decide +kernel

private theorem block50 : checkRange (checkAt EvaluationCheck) 7 6400 = true := by decide +kernel

private theorem block51 : checkRange (checkAt EvaluationCheck) 7 6528 = true := by decide +kernel

private theorem block52 : checkRange (checkAt EvaluationCheck) 7 6656 = true := by decide +kernel

private theorem block53 : checkRange (checkAt EvaluationCheck) 7 6784 = true := by decide +kernel

private theorem block54 : checkRange (checkAt EvaluationCheck) 7 6912 = true := by decide +kernel

private theorem block55 : checkRange (checkAt EvaluationCheck) 7 7040 = true := by decide +kernel

private theorem block56 : checkRange (checkAt EvaluationCheck) 7 7168 = true := by decide +kernel

private theorem block57 : checkRange (checkAt EvaluationCheck) 7 7296 = true := by decide +kernel

private theorem block58 : checkRange (checkAt EvaluationCheck) 7 7424 = true := by decide +kernel

private theorem block59 : checkRange (checkAt EvaluationCheck) 7 7552 = true := by decide +kernel

private theorem block60 : checkRange (checkAt EvaluationCheck) 7 7680 = true := by decide +kernel

private theorem block61 : checkRange (checkAt EvaluationCheck) 7 7808 = true := by decide +kernel

private theorem block62 : checkRange (checkAt EvaluationCheck) 7 7936 = true := by decide +kernel

private theorem block63 : checkRange (checkAt EvaluationCheck) 7 8064 = true := by decide +kernel

private theorem block64 : checkRange (checkAt EvaluationCheck) 7 8192 = true := by decide +kernel

private theorem block65 : checkRange (checkAt EvaluationCheck) 7 8320 = true := by decide +kernel

private theorem block66 : checkRange (checkAt EvaluationCheck) 7 8448 = true := by decide +kernel

private theorem block67 : checkRange (checkAt EvaluationCheck) 7 8576 = true := by decide +kernel

private theorem block68 : checkRange (checkAt EvaluationCheck) 7 8704 = true := by decide +kernel

private theorem block69 : checkRange (checkAt EvaluationCheck) 7 8832 = true := by decide +kernel

private theorem block70 : checkRange (checkAt EvaluationCheck) 7 8960 = true := by decide +kernel

private theorem block71 : checkRange (checkAt EvaluationCheck) 7 9088 = true := by decide +kernel

private theorem block72 : checkRange (checkAt EvaluationCheck) 7 9216 = true := by decide +kernel

private theorem block73 : checkRange (checkAt EvaluationCheck) 7 9344 = true := by decide +kernel

private theorem block74 : checkRange (checkAt EvaluationCheck) 7 9472 = true := by decide +kernel

private theorem block75 : checkRange (checkAt EvaluationCheck) 7 9600 = true := by decide +kernel

private theorem block76 : checkRange (checkAt EvaluationCheck) 7 9728 = true := by decide +kernel

private theorem block77 : checkRange (checkAt EvaluationCheck) 7 9856 = true := by decide +kernel

private theorem block78 : checkRange (checkAt EvaluationCheck) 7 9984 = true := by decide +kernel

private theorem block79 : checkRange (checkAt EvaluationCheck) 7 10112 = true := by decide +kernel

private theorem block80 : checkRange (checkAt EvaluationCheck) 7 10240 = true := by decide +kernel

private theorem block81 : checkRange (checkAt EvaluationCheck) 7 10368 = true := by decide +kernel

private theorem block82 : checkRange (checkAt EvaluationCheck) 7 10496 = true := by decide +kernel

private theorem block83 : checkRange (checkAt EvaluationCheck) 7 10624 = true := by decide +kernel

private theorem block84 : checkRange (checkAt EvaluationCheck) 7 10752 = true := by decide +kernel

private theorem block85 : checkRange (checkAt EvaluationCheck) 7 10880 = true := by decide +kernel

private theorem block86 : checkRange (checkAt EvaluationCheck) 7 11008 = true := by decide +kernel

private theorem block87 : checkRange (checkAt EvaluationCheck) 7 11136 = true := by decide +kernel

private theorem block88 : checkRange (checkAt EvaluationCheck) 7 11264 = true := by decide +kernel

private theorem block89 : checkRange (checkAt EvaluationCheck) 7 11392 = true := by decide +kernel

private theorem block90 : checkRange (checkAt EvaluationCheck) 7 11520 = true := by decide +kernel

private theorem block91 : checkRange (checkAt EvaluationCheck) 7 11648 = true := by decide +kernel

private theorem block92 : checkRange (checkAt EvaluationCheck) 7 11776 = true := by decide +kernel

private theorem block93 : checkRange (checkAt EvaluationCheck) 7 11904 = true := by decide +kernel

private theorem block94 : checkRange (checkAt EvaluationCheck) 7 12032 = true := by decide +kernel

private theorem block95 : checkRange (checkAt EvaluationCheck) 7 12160 = true := by decide +kernel

private theorem block96 : checkRange (checkAt EvaluationCheck) 7 12288 = true := by decide +kernel

private theorem block97 : checkRange (checkAt EvaluationCheck) 7 12416 = true := by decide +kernel

private theorem block98 : checkRange (checkAt EvaluationCheck) 7 12544 = true := by decide +kernel

private theorem block99 : checkRange (checkAt EvaluationCheck) 7 12672 = true := by decide +kernel

private theorem block100 : checkRange (checkAt EvaluationCheck) 7 12800 = true := by decide +kernel

private theorem block101 : checkRange (checkAt EvaluationCheck) 7 12928 = true := by decide +kernel

private theorem block102 : checkRange (checkAt EvaluationCheck) 7 13056 = true := by decide +kernel

private theorem block103 : checkRange (checkAt EvaluationCheck) 7 13184 = true := by decide +kernel

private theorem block104 : checkRange (checkAt EvaluationCheck) 7 13312 = true := by decide +kernel

private theorem block105 : checkRange (checkAt EvaluationCheck) 7 13440 = true := by decide +kernel

private theorem block106 : checkRange (checkAt EvaluationCheck) 7 13568 = true := by decide +kernel

private theorem block107 : checkRange (checkAt EvaluationCheck) 7 13696 = true := by decide +kernel

private theorem block108 : checkRange (checkAt EvaluationCheck) 7 13824 = true := by decide +kernel

private theorem block109 : checkRange (checkAt EvaluationCheck) 7 13952 = true := by decide +kernel

private theorem block110 : checkRange (checkAt EvaluationCheck) 7 14080 = true := by decide +kernel

private theorem block111 : checkRange (checkAt EvaluationCheck) 7 14208 = true := by decide +kernel

private theorem block112 : checkRange (checkAt EvaluationCheck) 7 14336 = true := by decide +kernel

private theorem block113 : checkRange (checkAt EvaluationCheck) 7 14464 = true := by decide +kernel

private theorem block114 : checkRange (checkAt EvaluationCheck) 7 14592 = true := by decide +kernel

private theorem block115 : checkRange (checkAt EvaluationCheck) 7 14720 = true := by decide +kernel

private theorem block116 : checkRange (checkAt EvaluationCheck) 7 14848 = true := by decide +kernel

private theorem block117 : checkRange (checkAt EvaluationCheck) 7 14976 = true := by decide +kernel

private theorem block118 : checkRange (checkAt EvaluationCheck) 7 15104 = true := by decide +kernel

private theorem block119 : checkRange (checkAt EvaluationCheck) 7 15232 = true := by decide +kernel

private theorem block120 : checkRange (checkAt EvaluationCheck) 7 15360 = true := by decide +kernel

private theorem block121 : checkRange (checkAt EvaluationCheck) 7 15488 = true := by decide +kernel

private theorem block122 : checkRange (checkAt EvaluationCheck) 7 15616 = true := by decide +kernel

private theorem block123 : checkRange (checkAt EvaluationCheck) 7 15744 = true := by decide +kernel

private theorem block124 : checkRange (checkAt EvaluationCheck) 7 15872 = true := by decide +kernel

private theorem block125 : checkRange (checkAt EvaluationCheck) 7 16000 = true := by decide +kernel

private theorem block126 : checkRange (checkAt EvaluationCheck) 7 16128 = true := by decide +kernel

private theorem block127 : checkRange (checkAt EvaluationCheck) 7 16256 = true := by decide +kernel

private theorem block128 : checkRange (checkAt EvaluationCheck) 7 16384 = true := by decide +kernel

private theorem block129 : checkRange (checkAt EvaluationCheck) 7 16512 = true := by decide +kernel

private theorem block130 : checkRange (checkAt EvaluationCheck) 7 16640 = true := by decide +kernel

private theorem block131 : checkRange (checkAt EvaluationCheck) 7 16768 = true := by decide +kernel

private theorem block132 : checkRange (checkAt EvaluationCheck) 7 16896 = true := by decide +kernel

private theorem block133 : checkRange (checkAt EvaluationCheck) 7 17024 = true := by decide +kernel

private theorem block134 : checkRange (checkAt EvaluationCheck) 7 17152 = true := by decide +kernel

private theorem block135 : checkRange (checkAt EvaluationCheck) 7 17280 = true := by decide +kernel

private theorem block136 : checkRange (checkAt EvaluationCheck) 7 17408 = true := by decide +kernel

private theorem block137 : checkRange (checkAt EvaluationCheck) 7 17536 = true := by decide +kernel

private theorem block138 : checkRange (checkAt EvaluationCheck) 7 17664 = true := by decide +kernel

private theorem block139 : checkRange (checkAt EvaluationCheck) 7 17792 = true := by decide +kernel

private theorem block140 : checkRange (checkAt EvaluationCheck) 7 17920 = true := by decide +kernel

private theorem block141 : checkRange (checkAt EvaluationCheck) 7 18048 = true := by decide +kernel

private theorem block142 : checkRange (checkAt EvaluationCheck) 7 18176 = true := by decide +kernel

private theorem block143 : checkRange (checkAt EvaluationCheck) 7 18304 = true := by decide +kernel

private theorem block144 : checkRange (checkAt EvaluationCheck) 7 18432 = true := by decide +kernel

private theorem block145 : checkRange (checkAt EvaluationCheck) 7 18560 = true := by decide +kernel

private theorem block146 : checkRange (checkAt EvaluationCheck) 7 18688 = true := by decide +kernel

private theorem block147 : checkRange (checkAt EvaluationCheck) 7 18816 = true := by decide +kernel

private theorem block148 : checkRange (checkAt EvaluationCheck) 7 18944 = true := by decide +kernel

private theorem block149 : checkRange (checkAt EvaluationCheck) 7 19072 = true := by decide +kernel

private theorem block150 : checkRange (checkAt EvaluationCheck) 7 19200 = true := by decide +kernel

private theorem block151 : checkRange (checkAt EvaluationCheck) 7 19328 = true := by decide +kernel

private theorem block152 : checkRange (checkAt EvaluationCheck) 7 19456 = true := by decide +kernel

private theorem block153 : checkRange (checkAt EvaluationCheck) 7 19584 = true := by decide +kernel

private theorem block154 : checkRange (checkAt EvaluationCheck) 7 19712 = true := by decide +kernel

private theorem block155 : checkRange (checkAt EvaluationCheck) 7 19840 = true := by decide +kernel

private theorem block156 : checkRange (checkAt EvaluationCheck) 7 19968 = true := by decide +kernel

private theorem block157 : checkRange (checkAt EvaluationCheck) 7 20096 = true := by decide +kernel

private theorem block158 : checkRange (checkAt EvaluationCheck) 7 20224 = true := by decide +kernel

private theorem block159 : checkRange (checkAt EvaluationCheck) 7 20352 = true := by decide +kernel

private theorem block160 : checkRange (checkAt EvaluationCheck) 7 20480 = true := by decide +kernel

private theorem block161 : checkRange (checkAt EvaluationCheck) 7 20608 = true := by decide +kernel

private theorem block162 : checkRange (checkAt EvaluationCheck) 7 20736 = true := by decide +kernel

private theorem block163 : checkRange (checkAt EvaluationCheck) 7 20864 = true := by decide +kernel

private theorem block164 : checkRange (checkAt EvaluationCheck) 7 20992 = true := by decide +kernel

private theorem block165 : checkRange (checkAt EvaluationCheck) 7 21120 = true := by decide +kernel

private theorem block166 : checkRange (checkAt EvaluationCheck) 7 21248 = true := by decide +kernel

private theorem block167 : checkRange (checkAt EvaluationCheck) 7 21376 = true := by decide +kernel

private theorem block168 : checkRange (checkAt EvaluationCheck) 7 21504 = true := by decide +kernel

private theorem block169 : checkRange (checkAt EvaluationCheck) 7 21632 = true := by decide +kernel

private theorem block170 : checkRange (checkAt EvaluationCheck) 7 21760 = true := by decide +kernel

private theorem block171 : checkRange (checkAt EvaluationCheck) 7 21888 = true := by decide +kernel

private theorem block172 : checkRange (checkAt EvaluationCheck) 7 22016 = true := by decide +kernel

private theorem block173 : checkRange (checkAt EvaluationCheck) 7 22144 = true := by decide +kernel

private theorem block174 : checkRange (checkAt EvaluationCheck) 7 22272 = true := by decide +kernel

private theorem block175 : checkRange (checkAt EvaluationCheck) 7 22400 = true := by decide +kernel

private theorem block176 : checkRange (checkAt EvaluationCheck) 7 22528 = true := by decide +kernel

private theorem block177 : checkRange (checkAt EvaluationCheck) 7 22656 = true := by decide +kernel

private theorem block178 : checkRange (checkAt EvaluationCheck) 7 22784 = true := by decide +kernel

private theorem block179 : checkRange (checkAt EvaluationCheck) 7 22912 = true := by decide +kernel

private theorem block180 : checkRange (checkAt EvaluationCheck) 7 23040 = true := by decide +kernel

private theorem block181 : checkRange (checkAt EvaluationCheck) 7 23168 = true := by decide +kernel

private theorem block182 : checkRange (checkAt EvaluationCheck) 7 23296 = true := by decide +kernel

private theorem block183 : checkRange (checkAt EvaluationCheck) 7 23424 = true := by decide +kernel

private theorem block184 : checkRange (checkAt EvaluationCheck) 7 23552 = true := by decide +kernel

private theorem block185 : checkRange (checkAt EvaluationCheck) 7 23680 = true := by decide +kernel

private theorem block186 : checkRange (checkAt EvaluationCheck) 7 23808 = true := by decide +kernel

private theorem block187 : checkRange (checkAt EvaluationCheck) 7 23936 = true := by decide +kernel

private theorem block188 : checkRange (checkAt EvaluationCheck) 7 24064 = true := by decide +kernel

private theorem block189 : checkRange (checkAt EvaluationCheck) 7 24192 = true := by decide +kernel

private theorem block190 : checkRange (checkAt EvaluationCheck) 7 24320 = true := by decide +kernel

private theorem block191 : checkRange (checkAt EvaluationCheck) 7 24448 = true := by decide +kernel

private theorem block192 : checkRange (checkAt EvaluationCheck) 7 24576 = true := by decide +kernel

private theorem block193 : checkRange (checkAt EvaluationCheck) 7 24704 = true := by decide +kernel

private theorem block194 : checkRange (checkAt EvaluationCheck) 7 24832 = true := by decide +kernel

private theorem block195 : checkRange (checkAt EvaluationCheck) 7 24960 = true := by decide +kernel

private theorem block196 : checkRange (checkAt EvaluationCheck) 7 25088 = true := by decide +kernel

private theorem block197 : checkRange (checkAt EvaluationCheck) 7 25216 = true := by decide +kernel

private theorem block198 : checkRange (checkAt EvaluationCheck) 7 25344 = true := by decide +kernel

private theorem block199 : checkRange (checkAt EvaluationCheck) 7 25472 = true := by decide +kernel

private theorem block200 : checkRange (checkAt EvaluationCheck) 7 25600 = true := by decide +kernel

private theorem block201 : checkRange (checkAt EvaluationCheck) 7 25728 = true := by decide +kernel

private theorem block202 : checkRange (checkAt EvaluationCheck) 7 25856 = true := by decide +kernel

private theorem block203 : checkRange (checkAt EvaluationCheck) 7 25984 = true := by decide +kernel

private theorem block204 : checkRange (checkAt EvaluationCheck) 7 26112 = true := by decide +kernel

private theorem block205 : checkRange (checkAt EvaluationCheck) 7 26240 = true := by decide +kernel

private theorem block206 : checkRange (checkAt EvaluationCheck) 7 26368 = true := by decide +kernel

private theorem block207 : checkRange (checkAt EvaluationCheck) 7 26496 = true := by decide +kernel

private theorem block208 : checkRange (checkAt EvaluationCheck) 7 26624 = true := by decide +kernel

private theorem block209 : checkRange (checkAt EvaluationCheck) 7 26752 = true := by decide +kernel

private theorem block210 : checkRange (checkAt EvaluationCheck) 7 26880 = true := by decide +kernel

private theorem block211 : checkRange (checkAt EvaluationCheck) 7 27008 = true := by decide +kernel

private theorem block212 : checkRange (checkAt EvaluationCheck) 7 27136 = true := by decide +kernel

private theorem block213 : checkRange (checkAt EvaluationCheck) 7 27264 = true := by decide +kernel

private theorem block214 : checkRange (checkAt EvaluationCheck) 7 27392 = true := by decide +kernel

private theorem block215 : checkRange (checkAt EvaluationCheck) 7 27520 = true := by decide +kernel

private theorem block216 : checkRange (checkAt EvaluationCheck) 7 27648 = true := by decide +kernel

private theorem block217 : checkRange (checkAt EvaluationCheck) 7 27776 = true := by decide +kernel

private theorem block218 : checkRange (checkAt EvaluationCheck) 7 27904 = true := by decide +kernel

private theorem block219 : checkRange (checkAt EvaluationCheck) 7 28032 = true := by decide +kernel

private theorem block220 : checkRange (checkAt EvaluationCheck) 7 28160 = true := by decide +kernel

private theorem block221 : checkRange (checkAt EvaluationCheck) 7 28288 = true := by decide +kernel

private theorem block222 : checkRange (checkAt EvaluationCheck) 7 28416 = true := by decide +kernel

private theorem block223 : checkRange (checkAt EvaluationCheck) 7 28544 = true := by decide +kernel

private theorem block224 : checkRange (checkAt EvaluationCheck) 7 28672 = true := by decide +kernel

private theorem block225 : checkRange (checkAt EvaluationCheck) 7 28800 = true := by decide +kernel

private theorem block226 : checkRange (checkAt EvaluationCheck) 7 28928 = true := by decide +kernel

private theorem block227 : checkRange (checkAt EvaluationCheck) 7 29056 = true := by decide +kernel

private theorem block228 : checkRange (checkAt EvaluationCheck) 7 29184 = true := by decide +kernel

private theorem block229 : checkRange (checkAt EvaluationCheck) 7 29312 = true := by decide +kernel

private theorem block230 : checkRange (checkAt EvaluationCheck) 7 29440 = true := by decide +kernel

private theorem block231 : checkRange (checkAt EvaluationCheck) 7 29568 = true := by decide +kernel

private theorem block232 : checkRange (checkAt EvaluationCheck) 7 29696 = true := by decide +kernel

private theorem block233 : checkRange (checkAt EvaluationCheck) 7 29824 = true := by decide +kernel

private theorem block234 : checkRange (checkAt EvaluationCheck) 7 29952 = true := by decide +kernel

private theorem block235 : checkRange (checkAt EvaluationCheck) 7 30080 = true := by decide +kernel

private theorem block236 : checkRange (checkAt EvaluationCheck) 7 30208 = true := by decide +kernel

private theorem block237 : checkRange (checkAt EvaluationCheck) 7 30336 = true := by decide +kernel

private theorem block238 : checkRange (checkAt EvaluationCheck) 7 30464 = true := by decide +kernel

private theorem block239 : checkRange (checkAt EvaluationCheck) 7 30592 = true := by decide +kernel

private theorem block240 : checkRange (checkAt EvaluationCheck) 7 30720 = true := by decide +kernel

private theorem block241 : checkRange (checkAt EvaluationCheck) 7 30848 = true := by decide +kernel

private theorem block242 : checkRange (checkAt EvaluationCheck) 7 30976 = true := by decide +kernel

private theorem block243 : checkRange (checkAt EvaluationCheck) 7 31104 = true := by decide +kernel

private theorem block244 : checkRange (checkAt EvaluationCheck) 7 31232 = true := by decide +kernel

private theorem block245 : checkRange (checkAt EvaluationCheck) 7 31360 = true := by decide +kernel

private theorem block246 : checkRange (checkAt EvaluationCheck) 7 31488 = true := by decide +kernel

private theorem block247 : checkRange (checkAt EvaluationCheck) 7 31616 = true := by decide +kernel

private theorem blocks (b : Fin 248) :
    checkRange (checkAt EvaluationCheck) 7 (2^7 * b.val) = true := by
  fin_cases b
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54
  · exact block55
  · exact block56
  · exact block57
  · exact block58
  · exact block59
  · exact block60
  · exact block61
  · exact block62
  · exact block63
  · exact block64
  · exact block65
  · exact block66
  · exact block67
  · exact block68
  · exact block69
  · exact block70
  · exact block71
  · exact block72
  · exact block73
  · exact block74
  · exact block75
  · exact block76
  · exact block77
  · exact block78
  · exact block79
  · exact block80
  · exact block81
  · exact block82
  · exact block83
  · exact block84
  · exact block85
  · exact block86
  · exact block87
  · exact block88
  · exact block89
  · exact block90
  · exact block91
  · exact block92
  · exact block93
  · exact block94
  · exact block95
  · exact block96
  · exact block97
  · exact block98
  · exact block99
  · exact block100
  · exact block101
  · exact block102
  · exact block103
  · exact block104
  · exact block105
  · exact block106
  · exact block107
  · exact block108
  · exact block109
  · exact block110
  · exact block111
  · exact block112
  · exact block113
  · exact block114
  · exact block115
  · exact block116
  · exact block117
  · exact block118
  · exact block119
  · exact block120
  · exact block121
  · exact block122
  · exact block123
  · exact block124
  · exact block125
  · exact block126
  · exact block127
  · exact block128
  · exact block129
  · exact block130
  · exact block131
  · exact block132
  · exact block133
  · exact block134
  · exact block135
  · exact block136
  · exact block137
  · exact block138
  · exact block139
  · exact block140
  · exact block141
  · exact block142
  · exact block143
  · exact block144
  · exact block145
  · exact block146
  · exact block147
  · exact block148
  · exact block149
  · exact block150
  · exact block151
  · exact block152
  · exact block153
  · exact block154
  · exact block155
  · exact block156
  · exact block157
  · exact block158
  · exact block159
  · exact block160
  · exact block161
  · exact block162
  · exact block163
  · exact block164
  · exact block165
  · exact block166
  · exact block167
  · exact block168
  · exact block169
  · exact block170
  · exact block171
  · exact block172
  · exact block173
  · exact block174
  · exact block175
  · exact block176
  · exact block177
  · exact block178
  · exact block179
  · exact block180
  · exact block181
  · exact block182
  · exact block183
  · exact block184
  · exact block185
  · exact block186
  · exact block187
  · exact block188
  · exact block189
  · exact block190
  · exact block191
  · exact block192
  · exact block193
  · exact block194
  · exact block195
  · exact block196
  · exact block197
  · exact block198
  · exact block199
  · exact block200
  · exact block201
  · exact block202
  · exact block203
  · exact block204
  · exact block205
  · exact block206
  · exact block207
  · exact block208
  · exact block209
  · exact block210
  · exact block211
  · exact block212
  · exact block213
  · exact block214
  · exact block215
  · exact block216
  · exact block217
  · exact block218
  · exact block219
  · exact block220
  · exact block221
  · exact block222
  · exact block223
  · exact block224
  · exact block225
  · exact block226
  · exact block227
  · exact block228
  · exact block229
  · exact block230
  · exact block231
  · exact block232
  · exact block233
  · exact block234
  · exact block235
  · exact block236
  · exact block237
  · exact block238
  · exact block239
  · exact block240
  · exact block241
  · exact block242
  · exact block243
  · exact block244
  · exact block245
  · exact block246
  · exact block247

theorem evaluationChecks (x : Fin 31671) : EvaluationCheck x :=
  of_check_blocks EvaluationCheck (by decide : 31671 ≤ 2^7 * 248) blocks x

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry
