module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.AuxiliaryData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check
/-!
# Checked short-map compositions for both candidate powers

Each kernel-checked block of 128 labels establishes the inverse witnesses and addition-chain
steps on the source labels. The ambient-word comparisons are separate results.
Source: the packed witnesses in `AuxiliaryData`, transcribed from the retained
ATLAS permutations and the exact `WordSetup` words.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks

private def pointTest (n : Nat) : Bool :=
  let i := Fin.ofNat 31671 n
  decide (uMap (uInvMap i) = i ∧ vMap (vInvMap i) = i ∧
    wMap (wInvMap i) = i ∧ sMap (sInvMap i) = i ∧
    a1Map i = wInvMap (rMap (vInvMap i)) ∧
    a2Map i = a1Map (a1Map i) ∧ a3Map i = a2Map (a1Map i) ∧
    a5Map i = a3Map (a2Map i) ∧ a10Map i = a5Map (a5Map i) ∧
    a15Map i = a10Map (a5Map i) ∧ sourceA i = a15Map (a15Map i) ∧
    b1Map i = uInvMap (vMap (vMap i)) ∧ b2Map i = b1Map (b1Map i) ∧
    b3Map i = b2Map (b1Map i) ∧ b6Map i = b3Map (b3Map i) ∧
    sourceB i = uMap (sMap (wMap (b6Map (wInvMap (sInvMap (uInvMap i)))))))

-- Release each bounded kernel-reduction cache before elaborating the next block.
set_option Elab.async false

private theorem block0 : checkPow pointTest 0 7 = true := by decide +kernel

private theorem block1 : checkPow pointTest 128 7 = true := by decide +kernel

private theorem block2 : checkPow pointTest 256 7 = true := by decide +kernel

private theorem block3 : checkPow pointTest 384 7 = true := by decide +kernel

private theorem block4 : checkPow pointTest 512 7 = true := by decide +kernel

private theorem block5 : checkPow pointTest 640 7 = true := by decide +kernel

private theorem block6 : checkPow pointTest 768 7 = true := by decide +kernel

private theorem block7 : checkPow pointTest 896 7 = true := by decide +kernel

private theorem block8 : checkPow pointTest 1024 7 = true := by decide +kernel

private theorem block9 : checkPow pointTest 1152 7 = true := by decide +kernel

private theorem block10 : checkPow pointTest 1280 7 = true := by decide +kernel

private theorem block11 : checkPow pointTest 1408 7 = true := by decide +kernel

private theorem block12 : checkPow pointTest 1536 7 = true := by decide +kernel

private theorem block13 : checkPow pointTest 1664 7 = true := by decide +kernel

private theorem block14 : checkPow pointTest 1792 7 = true := by decide +kernel

private theorem block15 : checkPow pointTest 1920 7 = true := by decide +kernel

private theorem block16 : checkPow pointTest 2048 7 = true := by decide +kernel

private theorem block17 : checkPow pointTest 2176 7 = true := by decide +kernel

private theorem block18 : checkPow pointTest 2304 7 = true := by decide +kernel

private theorem block19 : checkPow pointTest 2432 7 = true := by decide +kernel

private theorem block20 : checkPow pointTest 2560 7 = true := by decide +kernel

private theorem block21 : checkPow pointTest 2688 7 = true := by decide +kernel

private theorem block22 : checkPow pointTest 2816 7 = true := by decide +kernel

private theorem block23 : checkPow pointTest 2944 7 = true := by decide +kernel

private theorem block24 : checkPow pointTest 3072 7 = true := by decide +kernel

private theorem block25 : checkPow pointTest 3200 7 = true := by decide +kernel

private theorem block26 : checkPow pointTest 3328 7 = true := by decide +kernel

private theorem block27 : checkPow pointTest 3456 7 = true := by decide +kernel

private theorem block28 : checkPow pointTest 3584 7 = true := by decide +kernel

private theorem block29 : checkPow pointTest 3712 7 = true := by decide +kernel

private theorem block30 : checkPow pointTest 3840 7 = true := by decide +kernel

private theorem block31 : checkPow pointTest 3968 7 = true := by decide +kernel

private theorem block32 : checkPow pointTest 4096 7 = true := by decide +kernel

private theorem block33 : checkPow pointTest 4224 7 = true := by decide +kernel

private theorem block34 : checkPow pointTest 4352 7 = true := by decide +kernel

private theorem block35 : checkPow pointTest 4480 7 = true := by decide +kernel

private theorem block36 : checkPow pointTest 4608 7 = true := by decide +kernel

private theorem block37 : checkPow pointTest 4736 7 = true := by decide +kernel

private theorem block38 : checkPow pointTest 4864 7 = true := by decide +kernel

private theorem block39 : checkPow pointTest 4992 7 = true := by decide +kernel

private theorem block40 : checkPow pointTest 5120 7 = true := by decide +kernel

private theorem block41 : checkPow pointTest 5248 7 = true := by decide +kernel

private theorem block42 : checkPow pointTest 5376 7 = true := by decide +kernel

private theorem block43 : checkPow pointTest 5504 7 = true := by decide +kernel

private theorem block44 : checkPow pointTest 5632 7 = true := by decide +kernel

private theorem block45 : checkPow pointTest 5760 7 = true := by decide +kernel

private theorem block46 : checkPow pointTest 5888 7 = true := by decide +kernel

private theorem block47 : checkPow pointTest 6016 7 = true := by decide +kernel

private theorem block48 : checkPow pointTest 6144 7 = true := by decide +kernel

private theorem block49 : checkPow pointTest 6272 7 = true := by decide +kernel

private theorem block50 : checkPow pointTest 6400 7 = true := by decide +kernel

private theorem block51 : checkPow pointTest 6528 7 = true := by decide +kernel

private theorem block52 : checkPow pointTest 6656 7 = true := by decide +kernel

private theorem block53 : checkPow pointTest 6784 7 = true := by decide +kernel

private theorem block54 : checkPow pointTest 6912 7 = true := by decide +kernel

private theorem block55 : checkPow pointTest 7040 7 = true := by decide +kernel

private theorem block56 : checkPow pointTest 7168 7 = true := by decide +kernel

private theorem block57 : checkPow pointTest 7296 7 = true := by decide +kernel

private theorem block58 : checkPow pointTest 7424 7 = true := by decide +kernel

private theorem block59 : checkPow pointTest 7552 7 = true := by decide +kernel

private theorem block60 : checkPow pointTest 7680 7 = true := by decide +kernel

private theorem block61 : checkPow pointTest 7808 7 = true := by decide +kernel

private theorem block62 : checkPow pointTest 7936 7 = true := by decide +kernel

private theorem block63 : checkPow pointTest 8064 7 = true := by decide +kernel

private theorem block64 : checkPow pointTest 8192 7 = true := by decide +kernel

private theorem block65 : checkPow pointTest 8320 7 = true := by decide +kernel

private theorem block66 : checkPow pointTest 8448 7 = true := by decide +kernel

private theorem block67 : checkPow pointTest 8576 7 = true := by decide +kernel

private theorem block68 : checkPow pointTest 8704 7 = true := by decide +kernel

private theorem block69 : checkPow pointTest 8832 7 = true := by decide +kernel

private theorem block70 : checkPow pointTest 8960 7 = true := by decide +kernel

private theorem block71 : checkPow pointTest 9088 7 = true := by decide +kernel

private theorem block72 : checkPow pointTest 9216 7 = true := by decide +kernel

private theorem block73 : checkPow pointTest 9344 7 = true := by decide +kernel

private theorem block74 : checkPow pointTest 9472 7 = true := by decide +kernel

private theorem block75 : checkPow pointTest 9600 7 = true := by decide +kernel

private theorem block76 : checkPow pointTest 9728 7 = true := by decide +kernel

private theorem block77 : checkPow pointTest 9856 7 = true := by decide +kernel

private theorem block78 : checkPow pointTest 9984 7 = true := by decide +kernel

private theorem block79 : checkPow pointTest 10112 7 = true := by decide +kernel

private theorem block80 : checkPow pointTest 10240 7 = true := by decide +kernel

private theorem block81 : checkPow pointTest 10368 7 = true := by decide +kernel

private theorem block82 : checkPow pointTest 10496 7 = true := by decide +kernel

private theorem block83 : checkPow pointTest 10624 7 = true := by decide +kernel

private theorem block84 : checkPow pointTest 10752 7 = true := by decide +kernel

private theorem block85 : checkPow pointTest 10880 7 = true := by decide +kernel

private theorem block86 : checkPow pointTest 11008 7 = true := by decide +kernel

private theorem block87 : checkPow pointTest 11136 7 = true := by decide +kernel

private theorem block88 : checkPow pointTest 11264 7 = true := by decide +kernel

private theorem block89 : checkPow pointTest 11392 7 = true := by decide +kernel

private theorem block90 : checkPow pointTest 11520 7 = true := by decide +kernel

private theorem block91 : checkPow pointTest 11648 7 = true := by decide +kernel

private theorem block92 : checkPow pointTest 11776 7 = true := by decide +kernel

private theorem block93 : checkPow pointTest 11904 7 = true := by decide +kernel

private theorem block94 : checkPow pointTest 12032 7 = true := by decide +kernel

private theorem block95 : checkPow pointTest 12160 7 = true := by decide +kernel

private theorem block96 : checkPow pointTest 12288 7 = true := by decide +kernel

private theorem block97 : checkPow pointTest 12416 7 = true := by decide +kernel

private theorem block98 : checkPow pointTest 12544 7 = true := by decide +kernel

private theorem block99 : checkPow pointTest 12672 7 = true := by decide +kernel

private theorem block100 : checkPow pointTest 12800 7 = true := by decide +kernel

private theorem block101 : checkPow pointTest 12928 7 = true := by decide +kernel

private theorem block102 : checkPow pointTest 13056 7 = true := by decide +kernel

private theorem block103 : checkPow pointTest 13184 7 = true := by decide +kernel

private theorem block104 : checkPow pointTest 13312 7 = true := by decide +kernel

private theorem block105 : checkPow pointTest 13440 7 = true := by decide +kernel

private theorem block106 : checkPow pointTest 13568 7 = true := by decide +kernel

private theorem block107 : checkPow pointTest 13696 7 = true := by decide +kernel

private theorem block108 : checkPow pointTest 13824 7 = true := by decide +kernel

private theorem block109 : checkPow pointTest 13952 7 = true := by decide +kernel

private theorem block110 : checkPow pointTest 14080 7 = true := by decide +kernel

private theorem block111 : checkPow pointTest 14208 7 = true := by decide +kernel

private theorem block112 : checkPow pointTest 14336 7 = true := by decide +kernel

private theorem block113 : checkPow pointTest 14464 7 = true := by decide +kernel

private theorem block114 : checkPow pointTest 14592 7 = true := by decide +kernel

private theorem block115 : checkPow pointTest 14720 7 = true := by decide +kernel

private theorem block116 : checkPow pointTest 14848 7 = true := by decide +kernel

private theorem block117 : checkPow pointTest 14976 7 = true := by decide +kernel

private theorem block118 : checkPow pointTest 15104 7 = true := by decide +kernel

private theorem block119 : checkPow pointTest 15232 7 = true := by decide +kernel

private theorem block120 : checkPow pointTest 15360 7 = true := by decide +kernel

private theorem block121 : checkPow pointTest 15488 7 = true := by decide +kernel

private theorem block122 : checkPow pointTest 15616 7 = true := by decide +kernel

private theorem block123 : checkPow pointTest 15744 7 = true := by decide +kernel

private theorem block124 : checkPow pointTest 15872 7 = true := by decide +kernel

private theorem block125 : checkPow pointTest 16000 7 = true := by decide +kernel

private theorem block126 : checkPow pointTest 16128 7 = true := by decide +kernel

private theorem block127 : checkPow pointTest 16256 7 = true := by decide +kernel

private theorem block128 : checkPow pointTest 16384 7 = true := by decide +kernel

private theorem block129 : checkPow pointTest 16512 7 = true := by decide +kernel

private theorem block130 : checkPow pointTest 16640 7 = true := by decide +kernel

private theorem block131 : checkPow pointTest 16768 7 = true := by decide +kernel

private theorem block132 : checkPow pointTest 16896 7 = true := by decide +kernel

private theorem block133 : checkPow pointTest 17024 7 = true := by decide +kernel

private theorem block134 : checkPow pointTest 17152 7 = true := by decide +kernel

private theorem block135 : checkPow pointTest 17280 7 = true := by decide +kernel

private theorem block136 : checkPow pointTest 17408 7 = true := by decide +kernel

private theorem block137 : checkPow pointTest 17536 7 = true := by decide +kernel

private theorem block138 : checkPow pointTest 17664 7 = true := by decide +kernel

private theorem block139 : checkPow pointTest 17792 7 = true := by decide +kernel

private theorem block140 : checkPow pointTest 17920 7 = true := by decide +kernel

private theorem block141 : checkPow pointTest 18048 7 = true := by decide +kernel

private theorem block142 : checkPow pointTest 18176 7 = true := by decide +kernel

private theorem block143 : checkPow pointTest 18304 7 = true := by decide +kernel

private theorem block144 : checkPow pointTest 18432 7 = true := by decide +kernel

private theorem block145 : checkPow pointTest 18560 7 = true := by decide +kernel

private theorem block146 : checkPow pointTest 18688 7 = true := by decide +kernel

private theorem block147 : checkPow pointTest 18816 7 = true := by decide +kernel

private theorem block148 : checkPow pointTest 18944 7 = true := by decide +kernel

private theorem block149 : checkPow pointTest 19072 7 = true := by decide +kernel

private theorem block150 : checkPow pointTest 19200 7 = true := by decide +kernel

private theorem block151 : checkPow pointTest 19328 7 = true := by decide +kernel

private theorem block152 : checkPow pointTest 19456 7 = true := by decide +kernel

private theorem block153 : checkPow pointTest 19584 7 = true := by decide +kernel

private theorem block154 : checkPow pointTest 19712 7 = true := by decide +kernel

private theorem block155 : checkPow pointTest 19840 7 = true := by decide +kernel

private theorem block156 : checkPow pointTest 19968 7 = true := by decide +kernel

private theorem block157 : checkPow pointTest 20096 7 = true := by decide +kernel

private theorem block158 : checkPow pointTest 20224 7 = true := by decide +kernel

private theorem block159 : checkPow pointTest 20352 7 = true := by decide +kernel

private theorem block160 : checkPow pointTest 20480 7 = true := by decide +kernel

private theorem block161 : checkPow pointTest 20608 7 = true := by decide +kernel

private theorem block162 : checkPow pointTest 20736 7 = true := by decide +kernel

private theorem block163 : checkPow pointTest 20864 7 = true := by decide +kernel

private theorem block164 : checkPow pointTest 20992 7 = true := by decide +kernel

private theorem block165 : checkPow pointTest 21120 7 = true := by decide +kernel

private theorem block166 : checkPow pointTest 21248 7 = true := by decide +kernel

private theorem block167 : checkPow pointTest 21376 7 = true := by decide +kernel

private theorem block168 : checkPow pointTest 21504 7 = true := by decide +kernel

private theorem block169 : checkPow pointTest 21632 7 = true := by decide +kernel

private theorem block170 : checkPow pointTest 21760 7 = true := by decide +kernel

private theorem block171 : checkPow pointTest 21888 7 = true := by decide +kernel

private theorem block172 : checkPow pointTest 22016 7 = true := by decide +kernel

private theorem block173 : checkPow pointTest 22144 7 = true := by decide +kernel

private theorem block174 : checkPow pointTest 22272 7 = true := by decide +kernel

private theorem block175 : checkPow pointTest 22400 7 = true := by decide +kernel

private theorem block176 : checkPow pointTest 22528 7 = true := by decide +kernel

private theorem block177 : checkPow pointTest 22656 7 = true := by decide +kernel

private theorem block178 : checkPow pointTest 22784 7 = true := by decide +kernel

private theorem block179 : checkPow pointTest 22912 7 = true := by decide +kernel

private theorem block180 : checkPow pointTest 23040 7 = true := by decide +kernel

private theorem block181 : checkPow pointTest 23168 7 = true := by decide +kernel

private theorem block182 : checkPow pointTest 23296 7 = true := by decide +kernel

private theorem block183 : checkPow pointTest 23424 7 = true := by decide +kernel

private theorem block184 : checkPow pointTest 23552 7 = true := by decide +kernel

private theorem block185 : checkPow pointTest 23680 7 = true := by decide +kernel

private theorem block186 : checkPow pointTest 23808 7 = true := by decide +kernel

private theorem block187 : checkPow pointTest 23936 7 = true := by decide +kernel

private theorem block188 : checkPow pointTest 24064 7 = true := by decide +kernel

private theorem block189 : checkPow pointTest 24192 7 = true := by decide +kernel

private theorem block190 : checkPow pointTest 24320 7 = true := by decide +kernel

private theorem block191 : checkPow pointTest 24448 7 = true := by decide +kernel

private theorem block192 : checkPow pointTest 24576 7 = true := by decide +kernel

private theorem block193 : checkPow pointTest 24704 7 = true := by decide +kernel

private theorem block194 : checkPow pointTest 24832 7 = true := by decide +kernel

private theorem block195 : checkPow pointTest 24960 7 = true := by decide +kernel

private theorem block196 : checkPow pointTest 25088 7 = true := by decide +kernel

private theorem block197 : checkPow pointTest 25216 7 = true := by decide +kernel

private theorem block198 : checkPow pointTest 25344 7 = true := by decide +kernel

private theorem block199 : checkPow pointTest 25472 7 = true := by decide +kernel

private theorem block200 : checkPow pointTest 25600 7 = true := by decide +kernel

private theorem block201 : checkPow pointTest 25728 7 = true := by decide +kernel

private theorem block202 : checkPow pointTest 25856 7 = true := by decide +kernel

private theorem block203 : checkPow pointTest 25984 7 = true := by decide +kernel

private theorem block204 : checkPow pointTest 26112 7 = true := by decide +kernel

private theorem block205 : checkPow pointTest 26240 7 = true := by decide +kernel

private theorem block206 : checkPow pointTest 26368 7 = true := by decide +kernel

private theorem block207 : checkPow pointTest 26496 7 = true := by decide +kernel

private theorem block208 : checkPow pointTest 26624 7 = true := by decide +kernel

private theorem block209 : checkPow pointTest 26752 7 = true := by decide +kernel

private theorem block210 : checkPow pointTest 26880 7 = true := by decide +kernel

private theorem block211 : checkPow pointTest 27008 7 = true := by decide +kernel

private theorem block212 : checkPow pointTest 27136 7 = true := by decide +kernel

private theorem block213 : checkPow pointTest 27264 7 = true := by decide +kernel

private theorem block214 : checkPow pointTest 27392 7 = true := by decide +kernel

private theorem block215 : checkPow pointTest 27520 7 = true := by decide +kernel

private theorem block216 : checkPow pointTest 27648 7 = true := by decide +kernel

private theorem block217 : checkPow pointTest 27776 7 = true := by decide +kernel

private theorem block218 : checkPow pointTest 27904 7 = true := by decide +kernel

private theorem block219 : checkPow pointTest 28032 7 = true := by decide +kernel

private theorem block220 : checkPow pointTest 28160 7 = true := by decide +kernel

private theorem block221 : checkPow pointTest 28288 7 = true := by decide +kernel

private theorem block222 : checkPow pointTest 28416 7 = true := by decide +kernel

private theorem block223 : checkPow pointTest 28544 7 = true := by decide +kernel

private theorem block224 : checkPow pointTest 28672 7 = true := by decide +kernel

private theorem block225 : checkPow pointTest 28800 7 = true := by decide +kernel

private theorem block226 : checkPow pointTest 28928 7 = true := by decide +kernel

private theorem block227 : checkPow pointTest 29056 7 = true := by decide +kernel

private theorem block228 : checkPow pointTest 29184 7 = true := by decide +kernel

private theorem block229 : checkPow pointTest 29312 7 = true := by decide +kernel

private theorem block230 : checkPow pointTest 29440 7 = true := by decide +kernel

private theorem block231 : checkPow pointTest 29568 7 = true := by decide +kernel

private theorem block232 : checkPow pointTest 29696 7 = true := by decide +kernel

private theorem block233 : checkPow pointTest 29824 7 = true := by decide +kernel

private theorem block234 : checkPow pointTest 29952 7 = true := by decide +kernel

private theorem block235 : checkPow pointTest 30080 7 = true := by decide +kernel

private theorem block236 : checkPow pointTest 30208 7 = true := by decide +kernel

private theorem block237 : checkPow pointTest 30336 7 = true := by decide +kernel

private theorem block238 : checkPow pointTest 30464 7 = true := by decide +kernel

private theorem block239 : checkPow pointTest 30592 7 = true := by decide +kernel

private theorem block240 : checkPow pointTest 30720 7 = true := by decide +kernel

private theorem block241 : checkPow pointTest 30848 7 = true := by decide +kernel

private theorem block242 : checkPow pointTest 30976 7 = true := by decide +kernel

private theorem block243 : checkPow pointTest 31104 7 = true := by decide +kernel

private theorem block244 : checkPow pointTest 31232 7 = true := by decide +kernel

private theorem block245 : checkPow pointTest 31360 7 = true := by decide +kernel

private theorem block246 : checkPow pointTest 31488 7 = true := by decide +kernel

private theorem block247 : checkPow pointTest 31616 7 = true := by decide +kernel

private theorem block248 : checkPow pointTest 31744 7 = true := by decide +kernel

private theorem block249 : checkPow pointTest 31872 7 = true := by decide +kernel

private theorem block250 : checkPow pointTest 32000 7 = true := by decide +kernel

private theorem block251 : checkPow pointTest 32128 7 = true := by decide +kernel

private theorem block252 : checkPow pointTest 32256 7 = true := by decide +kernel

private theorem block253 : checkPow pointTest 32384 7 = true := by decide +kernel

private theorem block254 : checkPow pointTest 32512 7 = true := by decide +kernel

private theorem block255 : checkPow pointTest 32640 7 = true := by decide +kernel

private theorem all_checked : checkPow pointTest 0 15 = true :=
  (checkPow_join pointTest 14 0 (checkPow_join pointTest 13 0 (checkPow_join pointTest 12 0 (checkPow_join pointTest 11 0 (checkPow_join pointTest 10 0 (checkPow_join pointTest 9 0 (checkPow_join pointTest 8 0 (checkPow_join pointTest 7 0 block0 block1) (checkPow_join pointTest 7 256 block2 block3)) (checkPow_join pointTest 8 512 (checkPow_join pointTest 7 512 block4 block5) (checkPow_join pointTest 7 768 block6 block7))) (checkPow_join pointTest 9 1024 (checkPow_join pointTest 8 1024 (checkPow_join pointTest 7 1024 block8 block9) (checkPow_join pointTest 7 1280 block10 block11)) (checkPow_join pointTest 8 1536 (checkPow_join pointTest 7 1536 block12 block13) (checkPow_join pointTest 7 1792 block14 block15)))) (checkPow_join pointTest 10 2048 (checkPow_join pointTest 9 2048 (checkPow_join pointTest 8 2048 (checkPow_join pointTest 7 2048 block16 block17) (checkPow_join pointTest 7 2304 block18 block19)) (checkPow_join pointTest 8 2560 (checkPow_join pointTest 7 2560 block20 block21) (checkPow_join pointTest 7 2816 block22 block23))) (checkPow_join pointTest 9 3072 (checkPow_join pointTest 8 3072 (checkPow_join pointTest 7 3072 block24 block25) (checkPow_join pointTest 7 3328 block26 block27)) (checkPow_join pointTest 8 3584 (checkPow_join pointTest 7 3584 block28 block29) (checkPow_join pointTest 7 3840 block30 block31))))) (checkPow_join pointTest 11 4096 (checkPow_join pointTest 10 4096 (checkPow_join pointTest 9 4096 (checkPow_join pointTest 8 4096 (checkPow_join pointTest 7 4096 block32 block33) (checkPow_join pointTest 7 4352 block34 block35)) (checkPow_join pointTest 8 4608 (checkPow_join pointTest 7 4608 block36 block37) (checkPow_join pointTest 7 4864 block38 block39))) (checkPow_join pointTest 9 5120 (checkPow_join pointTest 8 5120 (checkPow_join pointTest 7 5120 block40 block41) (checkPow_join pointTest 7 5376 block42 block43)) (checkPow_join pointTest 8 5632 (checkPow_join pointTest 7 5632 block44 block45) (checkPow_join pointTest 7 5888 block46 block47)))) (checkPow_join pointTest 10 6144 (checkPow_join pointTest 9 6144 (checkPow_join pointTest 8 6144 (checkPow_join pointTest 7 6144 block48 block49) (checkPow_join pointTest 7 6400 block50 block51)) (checkPow_join pointTest 8 6656 (checkPow_join pointTest 7 6656 block52 block53) (checkPow_join pointTest 7 6912 block54 block55))) (checkPow_join pointTest 9 7168 (checkPow_join pointTest 8 7168 (checkPow_join pointTest 7 7168 block56 block57) (checkPow_join pointTest 7 7424 block58 block59)) (checkPow_join pointTest 8 7680 (checkPow_join pointTest 7 7680 block60 block61) (checkPow_join pointTest 7 7936 block62 block63)))))) (checkPow_join pointTest 12 8192 (checkPow_join pointTest 11 8192 (checkPow_join pointTest 10 8192 (checkPow_join pointTest 9 8192 (checkPow_join pointTest 8 8192 (checkPow_join pointTest 7 8192 block64 block65) (checkPow_join pointTest 7 8448 block66 block67)) (checkPow_join pointTest 8 8704 (checkPow_join pointTest 7 8704 block68 block69) (checkPow_join pointTest 7 8960 block70 block71))) (checkPow_join pointTest 9 9216 (checkPow_join pointTest 8 9216 (checkPow_join pointTest 7 9216 block72 block73) (checkPow_join pointTest 7 9472 block74 block75)) (checkPow_join pointTest 8 9728 (checkPow_join pointTest 7 9728 block76 block77) (checkPow_join pointTest 7 9984 block78 block79)))) (checkPow_join pointTest 10 10240 (checkPow_join pointTest 9 10240 (checkPow_join pointTest 8 10240 (checkPow_join pointTest 7 10240 block80 block81) (checkPow_join pointTest 7 10496 block82 block83)) (checkPow_join pointTest 8 10752 (checkPow_join pointTest 7 10752 block84 block85) (checkPow_join pointTest 7 11008 block86 block87))) (checkPow_join pointTest 9 11264 (checkPow_join pointTest 8 11264 (checkPow_join pointTest 7 11264 block88 block89) (checkPow_join pointTest 7 11520 block90 block91)) (checkPow_join pointTest 8 11776 (checkPow_join pointTest 7 11776 block92 block93) (checkPow_join pointTest 7 12032 block94 block95))))) (checkPow_join pointTest 11 12288 (checkPow_join pointTest 10 12288 (checkPow_join pointTest 9 12288 (checkPow_join pointTest 8 12288 (checkPow_join pointTest 7 12288 block96 block97) (checkPow_join pointTest 7 12544 block98 block99)) (checkPow_join pointTest 8 12800 (checkPow_join pointTest 7 12800 block100 block101) (checkPow_join pointTest 7 13056 block102 block103))) (checkPow_join pointTest 9 13312 (checkPow_join pointTest 8 13312 (checkPow_join pointTest 7 13312 block104 block105) (checkPow_join pointTest 7 13568 block106 block107)) (checkPow_join pointTest 8 13824 (checkPow_join pointTest 7 13824 block108 block109) (checkPow_join pointTest 7 14080 block110 block111)))) (checkPow_join pointTest 10 14336 (checkPow_join pointTest 9 14336 (checkPow_join pointTest 8 14336 (checkPow_join pointTest 7 14336 block112 block113) (checkPow_join pointTest 7 14592 block114 block115)) (checkPow_join pointTest 8 14848 (checkPow_join pointTest 7 14848 block116 block117) (checkPow_join pointTest 7 15104 block118 block119))) (checkPow_join pointTest 9 15360 (checkPow_join pointTest 8 15360 (checkPow_join pointTest 7 15360 block120 block121) (checkPow_join pointTest 7 15616 block122 block123)) (checkPow_join pointTest 8 15872 (checkPow_join pointTest 7 15872 block124 block125) (checkPow_join pointTest 7 16128 block126 block127))))))) (checkPow_join pointTest 13 16384 (checkPow_join pointTest 12 16384 (checkPow_join pointTest 11 16384 (checkPow_join pointTest 10 16384 (checkPow_join pointTest 9 16384 (checkPow_join pointTest 8 16384 (checkPow_join pointTest 7 16384 block128 block129) (checkPow_join pointTest 7 16640 block130 block131)) (checkPow_join pointTest 8 16896 (checkPow_join pointTest 7 16896 block132 block133) (checkPow_join pointTest 7 17152 block134 block135))) (checkPow_join pointTest 9 17408 (checkPow_join pointTest 8 17408 (checkPow_join pointTest 7 17408 block136 block137) (checkPow_join pointTest 7 17664 block138 block139)) (checkPow_join pointTest 8 17920 (checkPow_join pointTest 7 17920 block140 block141) (checkPow_join pointTest 7 18176 block142 block143)))) (checkPow_join pointTest 10 18432 (checkPow_join pointTest 9 18432 (checkPow_join pointTest 8 18432 (checkPow_join pointTest 7 18432 block144 block145) (checkPow_join pointTest 7 18688 block146 block147)) (checkPow_join pointTest 8 18944 (checkPow_join pointTest 7 18944 block148 block149) (checkPow_join pointTest 7 19200 block150 block151))) (checkPow_join pointTest 9 19456 (checkPow_join pointTest 8 19456 (checkPow_join pointTest 7 19456 block152 block153) (checkPow_join pointTest 7 19712 block154 block155)) (checkPow_join pointTest 8 19968 (checkPow_join pointTest 7 19968 block156 block157) (checkPow_join pointTest 7 20224 block158 block159))))) (checkPow_join pointTest 11 20480 (checkPow_join pointTest 10 20480 (checkPow_join pointTest 9 20480 (checkPow_join pointTest 8 20480 (checkPow_join pointTest 7 20480 block160 block161) (checkPow_join pointTest 7 20736 block162 block163)) (checkPow_join pointTest 8 20992 (checkPow_join pointTest 7 20992 block164 block165) (checkPow_join pointTest 7 21248 block166 block167))) (checkPow_join pointTest 9 21504 (checkPow_join pointTest 8 21504 (checkPow_join pointTest 7 21504 block168 block169) (checkPow_join pointTest 7 21760 block170 block171)) (checkPow_join pointTest 8 22016 (checkPow_join pointTest 7 22016 block172 block173) (checkPow_join pointTest 7 22272 block174 block175)))) (checkPow_join pointTest 10 22528 (checkPow_join pointTest 9 22528 (checkPow_join pointTest 8 22528 (checkPow_join pointTest 7 22528 block176 block177) (checkPow_join pointTest 7 22784 block178 block179)) (checkPow_join pointTest 8 23040 (checkPow_join pointTest 7 23040 block180 block181) (checkPow_join pointTest 7 23296 block182 block183))) (checkPow_join pointTest 9 23552 (checkPow_join pointTest 8 23552 (checkPow_join pointTest 7 23552 block184 block185) (checkPow_join pointTest 7 23808 block186 block187)) (checkPow_join pointTest 8 24064 (checkPow_join pointTest 7 24064 block188 block189) (checkPow_join pointTest 7 24320 block190 block191)))))) (checkPow_join pointTest 12 24576 (checkPow_join pointTest 11 24576 (checkPow_join pointTest 10 24576 (checkPow_join pointTest 9 24576 (checkPow_join pointTest 8 24576 (checkPow_join pointTest 7 24576 block192 block193) (checkPow_join pointTest 7 24832 block194 block195)) (checkPow_join pointTest 8 25088 (checkPow_join pointTest 7 25088 block196 block197) (checkPow_join pointTest 7 25344 block198 block199))) (checkPow_join pointTest 9 25600 (checkPow_join pointTest 8 25600 (checkPow_join pointTest 7 25600 block200 block201) (checkPow_join pointTest 7 25856 block202 block203)) (checkPow_join pointTest 8 26112 (checkPow_join pointTest 7 26112 block204 block205) (checkPow_join pointTest 7 26368 block206 block207)))) (checkPow_join pointTest 10 26624 (checkPow_join pointTest 9 26624 (checkPow_join pointTest 8 26624 (checkPow_join pointTest 7 26624 block208 block209) (checkPow_join pointTest 7 26880 block210 block211)) (checkPow_join pointTest 8 27136 (checkPow_join pointTest 7 27136 block212 block213) (checkPow_join pointTest 7 27392 block214 block215))) (checkPow_join pointTest 9 27648 (checkPow_join pointTest 8 27648 (checkPow_join pointTest 7 27648 block216 block217) (checkPow_join pointTest 7 27904 block218 block219)) (checkPow_join pointTest 8 28160 (checkPow_join pointTest 7 28160 block220 block221) (checkPow_join pointTest 7 28416 block222 block223))))) (checkPow_join pointTest 11 28672 (checkPow_join pointTest 10 28672 (checkPow_join pointTest 9 28672 (checkPow_join pointTest 8 28672 (checkPow_join pointTest 7 28672 block224 block225) (checkPow_join pointTest 7 28928 block226 block227)) (checkPow_join pointTest 8 29184 (checkPow_join pointTest 7 29184 block228 block229) (checkPow_join pointTest 7 29440 block230 block231))) (checkPow_join pointTest 9 29696 (checkPow_join pointTest 8 29696 (checkPow_join pointTest 7 29696 block232 block233) (checkPow_join pointTest 7 29952 block234 block235)) (checkPow_join pointTest 8 30208 (checkPow_join pointTest 7 30208 block236 block237) (checkPow_join pointTest 7 30464 block238 block239)))) (checkPow_join pointTest 10 30720 (checkPow_join pointTest 9 30720 (checkPow_join pointTest 8 30720 (checkPow_join pointTest 7 30720 block240 block241) (checkPow_join pointTest 7 30976 block242 block243)) (checkPow_join pointTest 8 31232 (checkPow_join pointTest 7 31232 block244 block245) (checkPow_join pointTest 7 31488 block246 block247))) (checkPow_join pointTest 9 31744 (checkPow_join pointTest 8 31744 (checkPow_join pointTest 7 31744 block248 block249) (checkPow_join pointTest 7 32000 block250 block251)) (checkPow_join pointTest 8 32256 (checkPow_join pointTest 7 32256 block252 block253) (checkPow_join pointTest 7 32512 block254 block255))))))))

private theorem point_properties (i : Fin 31671) :
  uMap (uInvMap i) = i ∧ vMap (vInvMap i) = i ∧
    wMap (wInvMap i) = i ∧ sMap (sInvMap i) = i ∧
    a1Map i = wInvMap (rMap (vInvMap i)) ∧
    a2Map i = a1Map (a1Map i) ∧ a3Map i = a2Map (a1Map i) ∧
    a5Map i = a3Map (a2Map i) ∧ a10Map i = a5Map (a5Map i) ∧
    a15Map i = a10Map (a5Map i) ∧ sourceA i = a15Map (a15Map i) ∧
    b1Map i = uInvMap (vMap (vMap i)) ∧ b2Map i = b1Map (b1Map i) ∧
    b3Map i = b2Map (b1Map i) ∧ b6Map i = b3Map (b3Map i) ∧
    sourceB i = uMap (sMap (wMap (b6Map (wInvMap (sInvMap (uInvMap i)))))) := by
  have h := checkPow_sound pointTest 15 0 all_checked i.val
    (Nat.zero_le _) (Nat.lt_trans i.isLt (by decide))
  have hi : Fin.ofNat 31671 i.val = i := by simp
  simpa only [pointTest, hi, decide_eq_true_eq] using h

theorem uMap_right_inv (i : Fin 31671) : uMap (uInvMap i) = i :=
  (point_properties i).1

theorem vMap_right_inv (i : Fin 31671) : vMap (vInvMap i) = i :=
  (point_properties i).2.1

theorem wMap_right_inv (i : Fin 31671) : wMap (wInvMap i) = i :=
  (point_properties i).2.2.1

theorem sMap_right_inv (i : Fin 31671) : sMap (sInvMap i) = i :=
  (point_properties i).2.2.2.1

theorem a1Map_spec (i : Fin 31671) : a1Map i = wInvMap (rMap (vInvMap i)) :=
  (point_properties i).2.2.2.2.1

theorem a2Map_spec (i : Fin 31671) : a2Map i = a1Map (a1Map i) :=
  (point_properties i).2.2.2.2.2.1

theorem a3Map_spec (i : Fin 31671) : a3Map i = a2Map (a1Map i) :=
  (point_properties i).2.2.2.2.2.2.1

theorem a5Map_spec (i : Fin 31671) : a5Map i = a3Map (a2Map i) :=
  (point_properties i).2.2.2.2.2.2.2.1

theorem a10Map_spec (i : Fin 31671) : a10Map i = a5Map (a5Map i) :=
  (point_properties i).2.2.2.2.2.2.2.2.1

theorem a15Map_spec (i : Fin 31671) : a15Map i = a10Map (a5Map i) :=
  (point_properties i).2.2.2.2.2.2.2.2.2.1

theorem sourceA_spec (i : Fin 31671) : sourceA i = a15Map (a15Map i) :=
  (point_properties i).2.2.2.2.2.2.2.2.2.2.1

theorem b1Map_spec (i : Fin 31671) : b1Map i = uInvMap (vMap (vMap i)) :=
  (point_properties i).2.2.2.2.2.2.2.2.2.2.2.1

theorem b2Map_spec (i : Fin 31671) : b2Map i = b1Map (b1Map i) :=
  (point_properties i).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem b3Map_spec (i : Fin 31671) : b3Map i = b2Map (b1Map i) :=
  (point_properties i).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem b6Map_spec (i : Fin 31671) : b6Map i = b3Map (b3Map i) :=
  (point_properties i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sourceB_spec (i : Fin 31671) : sourceB i = uMap (sMap (wMap (b6Map (wInvMap (sInvMap (uInvMap i)))))) :=
  (point_properties i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks
