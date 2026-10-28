module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.InverseChecks.Check

/-!
# Exhaustive cancellation for the packed ambient `b` map

Each block checks 1024 points with `decide +kernel`. Adjacent blocks are joined
by the proved balanced-check rule, covering all 306936 ambient points. The
last block uses `Fin.ofNat`, so its harmless padding checks valid points again.
Declaration elaboration is serial to release each bounded reduction cache.

Source: the existing `GeneratorData` packed transcription of the retained
ATLAS F24G1-p306936B0 tables, with attribution in `AtlasCarriers/source/README.md`.
Reproduce proof syntax with `InverseChecks/source/generate.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks

open InverseChecks

private abbrev pointTest := inversePointTest bMap bInvMap

set_option Elab.async false

private theorem block0 : checkPow pointTest 0 10 = true :=
  by decide +kernel

private theorem block1 : checkPow pointTest 1024 10 = true :=
  by decide +kernel

private theorem block2 : checkPow pointTest 2048 10 = true :=
  by decide +kernel

private theorem block3 : checkPow pointTest 3072 10 = true :=
  by decide +kernel

private theorem block4 : checkPow pointTest 4096 10 = true :=
  by decide +kernel

private theorem block5 : checkPow pointTest 5120 10 = true :=
  by decide +kernel

private theorem block6 : checkPow pointTest 6144 10 = true :=
  by decide +kernel

private theorem block7 : checkPow pointTest 7168 10 = true :=
  by decide +kernel

private theorem block8 : checkPow pointTest 8192 10 = true :=
  by decide +kernel

private theorem block9 : checkPow pointTest 9216 10 = true :=
  by decide +kernel

private theorem block10 : checkPow pointTest 10240 10 = true :=
  by decide +kernel

private theorem block11 : checkPow pointTest 11264 10 = true :=
  by decide +kernel

private theorem block12 : checkPow pointTest 12288 10 = true :=
  by decide +kernel

private theorem block13 : checkPow pointTest 13312 10 = true :=
  by decide +kernel

private theorem block14 : checkPow pointTest 14336 10 = true :=
  by decide +kernel

private theorem block15 : checkPow pointTest 15360 10 = true :=
  by decide +kernel

private theorem block16 : checkPow pointTest 16384 10 = true :=
  by decide +kernel

private theorem block17 : checkPow pointTest 17408 10 = true :=
  by decide +kernel

private theorem block18 : checkPow pointTest 18432 10 = true :=
  by decide +kernel

private theorem block19 : checkPow pointTest 19456 10 = true :=
  by decide +kernel

private theorem block20 : checkPow pointTest 20480 10 = true :=
  by decide +kernel

private theorem block21 : checkPow pointTest 21504 10 = true :=
  by decide +kernel

private theorem block22 : checkPow pointTest 22528 10 = true :=
  by decide +kernel

private theorem block23 : checkPow pointTest 23552 10 = true :=
  by decide +kernel

private theorem block24 : checkPow pointTest 24576 10 = true :=
  by decide +kernel

private theorem block25 : checkPow pointTest 25600 10 = true :=
  by decide +kernel

private theorem block26 : checkPow pointTest 26624 10 = true :=
  by decide +kernel

private theorem block27 : checkPow pointTest 27648 10 = true :=
  by decide +kernel

private theorem block28 : checkPow pointTest 28672 10 = true :=
  by decide +kernel

private theorem block29 : checkPow pointTest 29696 10 = true :=
  by decide +kernel

private theorem block30 : checkPow pointTest 30720 10 = true :=
  by decide +kernel

private theorem block31 : checkPow pointTest 31744 10 = true :=
  by decide +kernel

private theorem block32 : checkPow pointTest 32768 10 = true :=
  by decide +kernel

private theorem block33 : checkPow pointTest 33792 10 = true :=
  by decide +kernel

private theorem block34 : checkPow pointTest 34816 10 = true :=
  by decide +kernel

private theorem block35 : checkPow pointTest 35840 10 = true :=
  by decide +kernel

private theorem block36 : checkPow pointTest 36864 10 = true :=
  by decide +kernel

private theorem block37 : checkPow pointTest 37888 10 = true :=
  by decide +kernel

private theorem block38 : checkPow pointTest 38912 10 = true :=
  by decide +kernel

private theorem block39 : checkPow pointTest 39936 10 = true :=
  by decide +kernel

private theorem block40 : checkPow pointTest 40960 10 = true :=
  by decide +kernel

private theorem block41 : checkPow pointTest 41984 10 = true :=
  by decide +kernel

private theorem block42 : checkPow pointTest 43008 10 = true :=
  by decide +kernel

private theorem block43 : checkPow pointTest 44032 10 = true :=
  by decide +kernel

private theorem block44 : checkPow pointTest 45056 10 = true :=
  by decide +kernel

private theorem block45 : checkPow pointTest 46080 10 = true :=
  by decide +kernel

private theorem block46 : checkPow pointTest 47104 10 = true :=
  by decide +kernel

private theorem block47 : checkPow pointTest 48128 10 = true :=
  by decide +kernel

private theorem block48 : checkPow pointTest 49152 10 = true :=
  by decide +kernel

private theorem block49 : checkPow pointTest 50176 10 = true :=
  by decide +kernel

private theorem block50 : checkPow pointTest 51200 10 = true :=
  by decide +kernel

private theorem block51 : checkPow pointTest 52224 10 = true :=
  by decide +kernel

private theorem block52 : checkPow pointTest 53248 10 = true :=
  by decide +kernel

private theorem block53 : checkPow pointTest 54272 10 = true :=
  by decide +kernel

private theorem block54 : checkPow pointTest 55296 10 = true :=
  by decide +kernel

private theorem block55 : checkPow pointTest 56320 10 = true :=
  by decide +kernel

private theorem block56 : checkPow pointTest 57344 10 = true :=
  by decide +kernel

private theorem block57 : checkPow pointTest 58368 10 = true :=
  by decide +kernel

private theorem block58 : checkPow pointTest 59392 10 = true :=
  by decide +kernel

private theorem block59 : checkPow pointTest 60416 10 = true :=
  by decide +kernel

private theorem block60 : checkPow pointTest 61440 10 = true :=
  by decide +kernel

private theorem block61 : checkPow pointTest 62464 10 = true :=
  by decide +kernel

private theorem block62 : checkPow pointTest 63488 10 = true :=
  by decide +kernel

private theorem block63 : checkPow pointTest 64512 10 = true :=
  by decide +kernel

private theorem block64 : checkPow pointTest 65536 10 = true :=
  by decide +kernel

private theorem block65 : checkPow pointTest 66560 10 = true :=
  by decide +kernel

private theorem block66 : checkPow pointTest 67584 10 = true :=
  by decide +kernel

private theorem block67 : checkPow pointTest 68608 10 = true :=
  by decide +kernel

private theorem block68 : checkPow pointTest 69632 10 = true :=
  by decide +kernel

private theorem block69 : checkPow pointTest 70656 10 = true :=
  by decide +kernel

private theorem block70 : checkPow pointTest 71680 10 = true :=
  by decide +kernel

private theorem block71 : checkPow pointTest 72704 10 = true :=
  by decide +kernel

private theorem block72 : checkPow pointTest 73728 10 = true :=
  by decide +kernel

private theorem block73 : checkPow pointTest 74752 10 = true :=
  by decide +kernel

private theorem block74 : checkPow pointTest 75776 10 = true :=
  by decide +kernel

private theorem block75 : checkPow pointTest 76800 10 = true :=
  by decide +kernel

private theorem block76 : checkPow pointTest 77824 10 = true :=
  by decide +kernel

private theorem block77 : checkPow pointTest 78848 10 = true :=
  by decide +kernel

private theorem block78 : checkPow pointTest 79872 10 = true :=
  by decide +kernel

private theorem block79 : checkPow pointTest 80896 10 = true :=
  by decide +kernel

private theorem block80 : checkPow pointTest 81920 10 = true :=
  by decide +kernel

private theorem block81 : checkPow pointTest 82944 10 = true :=
  by decide +kernel

private theorem block82 : checkPow pointTest 83968 10 = true :=
  by decide +kernel

private theorem block83 : checkPow pointTest 84992 10 = true :=
  by decide +kernel

private theorem block84 : checkPow pointTest 86016 10 = true :=
  by decide +kernel

private theorem block85 : checkPow pointTest 87040 10 = true :=
  by decide +kernel

private theorem block86 : checkPow pointTest 88064 10 = true :=
  by decide +kernel

private theorem block87 : checkPow pointTest 89088 10 = true :=
  by decide +kernel

private theorem block88 : checkPow pointTest 90112 10 = true :=
  by decide +kernel

private theorem block89 : checkPow pointTest 91136 10 = true :=
  by decide +kernel

private theorem block90 : checkPow pointTest 92160 10 = true :=
  by decide +kernel

private theorem block91 : checkPow pointTest 93184 10 = true :=
  by decide +kernel

private theorem block92 : checkPow pointTest 94208 10 = true :=
  by decide +kernel

private theorem block93 : checkPow pointTest 95232 10 = true :=
  by decide +kernel

private theorem block94 : checkPow pointTest 96256 10 = true :=
  by decide +kernel

private theorem block95 : checkPow pointTest 97280 10 = true :=
  by decide +kernel

private theorem block96 : checkPow pointTest 98304 10 = true :=
  by decide +kernel

private theorem block97 : checkPow pointTest 99328 10 = true :=
  by decide +kernel

private theorem block98 : checkPow pointTest 100352 10 = true :=
  by decide +kernel

private theorem block99 : checkPow pointTest 101376 10 = true :=
  by decide +kernel

private theorem block100 : checkPow pointTest 102400 10 = true :=
  by decide +kernel

private theorem block101 : checkPow pointTest 103424 10 = true :=
  by decide +kernel

private theorem block102 : checkPow pointTest 104448 10 = true :=
  by decide +kernel

private theorem block103 : checkPow pointTest 105472 10 = true :=
  by decide +kernel

private theorem block104 : checkPow pointTest 106496 10 = true :=
  by decide +kernel

private theorem block105 : checkPow pointTest 107520 10 = true :=
  by decide +kernel

private theorem block106 : checkPow pointTest 108544 10 = true :=
  by decide +kernel

private theorem block107 : checkPow pointTest 109568 10 = true :=
  by decide +kernel

private theorem block108 : checkPow pointTest 110592 10 = true :=
  by decide +kernel

private theorem block109 : checkPow pointTest 111616 10 = true :=
  by decide +kernel

private theorem block110 : checkPow pointTest 112640 10 = true :=
  by decide +kernel

private theorem block111 : checkPow pointTest 113664 10 = true :=
  by decide +kernel

private theorem block112 : checkPow pointTest 114688 10 = true :=
  by decide +kernel

private theorem block113 : checkPow pointTest 115712 10 = true :=
  by decide +kernel

private theorem block114 : checkPow pointTest 116736 10 = true :=
  by decide +kernel

private theorem block115 : checkPow pointTest 117760 10 = true :=
  by decide +kernel

private theorem block116 : checkPow pointTest 118784 10 = true :=
  by decide +kernel

private theorem block117 : checkPow pointTest 119808 10 = true :=
  by decide +kernel

private theorem block118 : checkPow pointTest 120832 10 = true :=
  by decide +kernel

private theorem block119 : checkPow pointTest 121856 10 = true :=
  by decide +kernel

private theorem block120 : checkPow pointTest 122880 10 = true :=
  by decide +kernel

private theorem block121 : checkPow pointTest 123904 10 = true :=
  by decide +kernel

private theorem block122 : checkPow pointTest 124928 10 = true :=
  by decide +kernel

private theorem block123 : checkPow pointTest 125952 10 = true :=
  by decide +kernel

private theorem block124 : checkPow pointTest 126976 10 = true :=
  by decide +kernel

private theorem block125 : checkPow pointTest 128000 10 = true :=
  by decide +kernel

private theorem block126 : checkPow pointTest 129024 10 = true :=
  by decide +kernel

private theorem block127 : checkPow pointTest 130048 10 = true :=
  by decide +kernel

private theorem block128 : checkPow pointTest 131072 10 = true :=
  by decide +kernel

private theorem block129 : checkPow pointTest 132096 10 = true :=
  by decide +kernel

private theorem block130 : checkPow pointTest 133120 10 = true :=
  by decide +kernel

private theorem block131 : checkPow pointTest 134144 10 = true :=
  by decide +kernel

private theorem block132 : checkPow pointTest 135168 10 = true :=
  by decide +kernel

private theorem block133 : checkPow pointTest 136192 10 = true :=
  by decide +kernel

private theorem block134 : checkPow pointTest 137216 10 = true :=
  by decide +kernel

private theorem block135 : checkPow pointTest 138240 10 = true :=
  by decide +kernel

private theorem block136 : checkPow pointTest 139264 10 = true :=
  by decide +kernel

private theorem block137 : checkPow pointTest 140288 10 = true :=
  by decide +kernel

private theorem block138 : checkPow pointTest 141312 10 = true :=
  by decide +kernel

private theorem block139 : checkPow pointTest 142336 10 = true :=
  by decide +kernel

private theorem block140 : checkPow pointTest 143360 10 = true :=
  by decide +kernel

private theorem block141 : checkPow pointTest 144384 10 = true :=
  by decide +kernel

private theorem block142 : checkPow pointTest 145408 10 = true :=
  by decide +kernel

private theorem block143 : checkPow pointTest 146432 10 = true :=
  by decide +kernel

private theorem block144 : checkPow pointTest 147456 10 = true :=
  by decide +kernel

private theorem block145 : checkPow pointTest 148480 10 = true :=
  by decide +kernel

private theorem block146 : checkPow pointTest 149504 10 = true :=
  by decide +kernel

private theorem block147 : checkPow pointTest 150528 10 = true :=
  by decide +kernel

private theorem block148 : checkPow pointTest 151552 10 = true :=
  by decide +kernel

private theorem block149 : checkPow pointTest 152576 10 = true :=
  by decide +kernel

private theorem block150 : checkPow pointTest 153600 10 = true :=
  by decide +kernel

private theorem block151 : checkPow pointTest 154624 10 = true :=
  by decide +kernel

private theorem block152 : checkPow pointTest 155648 10 = true :=
  by decide +kernel

private theorem block153 : checkPow pointTest 156672 10 = true :=
  by decide +kernel

private theorem block154 : checkPow pointTest 157696 10 = true :=
  by decide +kernel

private theorem block155 : checkPow pointTest 158720 10 = true :=
  by decide +kernel

private theorem block156 : checkPow pointTest 159744 10 = true :=
  by decide +kernel

private theorem block157 : checkPow pointTest 160768 10 = true :=
  by decide +kernel

private theorem block158 : checkPow pointTest 161792 10 = true :=
  by decide +kernel

private theorem block159 : checkPow pointTest 162816 10 = true :=
  by decide +kernel

private theorem block160 : checkPow pointTest 163840 10 = true :=
  by decide +kernel

private theorem block161 : checkPow pointTest 164864 10 = true :=
  by decide +kernel

private theorem block162 : checkPow pointTest 165888 10 = true :=
  by decide +kernel

private theorem block163 : checkPow pointTest 166912 10 = true :=
  by decide +kernel

private theorem block164 : checkPow pointTest 167936 10 = true :=
  by decide +kernel

private theorem block165 : checkPow pointTest 168960 10 = true :=
  by decide +kernel

private theorem block166 : checkPow pointTest 169984 10 = true :=
  by decide +kernel

private theorem block167 : checkPow pointTest 171008 10 = true :=
  by decide +kernel

private theorem block168 : checkPow pointTest 172032 10 = true :=
  by decide +kernel

private theorem block169 : checkPow pointTest 173056 10 = true :=
  by decide +kernel

private theorem block170 : checkPow pointTest 174080 10 = true :=
  by decide +kernel

private theorem block171 : checkPow pointTest 175104 10 = true :=
  by decide +kernel

private theorem block172 : checkPow pointTest 176128 10 = true :=
  by decide +kernel

private theorem block173 : checkPow pointTest 177152 10 = true :=
  by decide +kernel

private theorem block174 : checkPow pointTest 178176 10 = true :=
  by decide +kernel

private theorem block175 : checkPow pointTest 179200 10 = true :=
  by decide +kernel

private theorem block176 : checkPow pointTest 180224 10 = true :=
  by decide +kernel

private theorem block177 : checkPow pointTest 181248 10 = true :=
  by decide +kernel

private theorem block178 : checkPow pointTest 182272 10 = true :=
  by decide +kernel

private theorem block179 : checkPow pointTest 183296 10 = true :=
  by decide +kernel

private theorem block180 : checkPow pointTest 184320 10 = true :=
  by decide +kernel

private theorem block181 : checkPow pointTest 185344 10 = true :=
  by decide +kernel

private theorem block182 : checkPow pointTest 186368 10 = true :=
  by decide +kernel

private theorem block183 : checkPow pointTest 187392 10 = true :=
  by decide +kernel

private theorem block184 : checkPow pointTest 188416 10 = true :=
  by decide +kernel

private theorem block185 : checkPow pointTest 189440 10 = true :=
  by decide +kernel

private theorem block186 : checkPow pointTest 190464 10 = true :=
  by decide +kernel

private theorem block187 : checkPow pointTest 191488 10 = true :=
  by decide +kernel

private theorem block188 : checkPow pointTest 192512 10 = true :=
  by decide +kernel

private theorem block189 : checkPow pointTest 193536 10 = true :=
  by decide +kernel

private theorem block190 : checkPow pointTest 194560 10 = true :=
  by decide +kernel

private theorem block191 : checkPow pointTest 195584 10 = true :=
  by decide +kernel

private theorem block192 : checkPow pointTest 196608 10 = true :=
  by decide +kernel

private theorem block193 : checkPow pointTest 197632 10 = true :=
  by decide +kernel

private theorem block194 : checkPow pointTest 198656 10 = true :=
  by decide +kernel

private theorem block195 : checkPow pointTest 199680 10 = true :=
  by decide +kernel

private theorem block196 : checkPow pointTest 200704 10 = true :=
  by decide +kernel

private theorem block197 : checkPow pointTest 201728 10 = true :=
  by decide +kernel

private theorem block198 : checkPow pointTest 202752 10 = true :=
  by decide +kernel

private theorem block199 : checkPow pointTest 203776 10 = true :=
  by decide +kernel

private theorem block200 : checkPow pointTest 204800 10 = true :=
  by decide +kernel

private theorem block201 : checkPow pointTest 205824 10 = true :=
  by decide +kernel

private theorem block202 : checkPow pointTest 206848 10 = true :=
  by decide +kernel

private theorem block203 : checkPow pointTest 207872 10 = true :=
  by decide +kernel

private theorem block204 : checkPow pointTest 208896 10 = true :=
  by decide +kernel

private theorem block205 : checkPow pointTest 209920 10 = true :=
  by decide +kernel

private theorem block206 : checkPow pointTest 210944 10 = true :=
  by decide +kernel

private theorem block207 : checkPow pointTest 211968 10 = true :=
  by decide +kernel

private theorem block208 : checkPow pointTest 212992 10 = true :=
  by decide +kernel

private theorem block209 : checkPow pointTest 214016 10 = true :=
  by decide +kernel

private theorem block210 : checkPow pointTest 215040 10 = true :=
  by decide +kernel

private theorem block211 : checkPow pointTest 216064 10 = true :=
  by decide +kernel

private theorem block212 : checkPow pointTest 217088 10 = true :=
  by decide +kernel

private theorem block213 : checkPow pointTest 218112 10 = true :=
  by decide +kernel

private theorem block214 : checkPow pointTest 219136 10 = true :=
  by decide +kernel

private theorem block215 : checkPow pointTest 220160 10 = true :=
  by decide +kernel

private theorem block216 : checkPow pointTest 221184 10 = true :=
  by decide +kernel

private theorem block217 : checkPow pointTest 222208 10 = true :=
  by decide +kernel

private theorem block218 : checkPow pointTest 223232 10 = true :=
  by decide +kernel

private theorem block219 : checkPow pointTest 224256 10 = true :=
  by decide +kernel

private theorem block220 : checkPow pointTest 225280 10 = true :=
  by decide +kernel

private theorem block221 : checkPow pointTest 226304 10 = true :=
  by decide +kernel

private theorem block222 : checkPow pointTest 227328 10 = true :=
  by decide +kernel

private theorem block223 : checkPow pointTest 228352 10 = true :=
  by decide +kernel

private theorem block224 : checkPow pointTest 229376 10 = true :=
  by decide +kernel

private theorem block225 : checkPow pointTest 230400 10 = true :=
  by decide +kernel

private theorem block226 : checkPow pointTest 231424 10 = true :=
  by decide +kernel

private theorem block227 : checkPow pointTest 232448 10 = true :=
  by decide +kernel

private theorem block228 : checkPow pointTest 233472 10 = true :=
  by decide +kernel

private theorem block229 : checkPow pointTest 234496 10 = true :=
  by decide +kernel

private theorem block230 : checkPow pointTest 235520 10 = true :=
  by decide +kernel

private theorem block231 : checkPow pointTest 236544 10 = true :=
  by decide +kernel

private theorem block232 : checkPow pointTest 237568 10 = true :=
  by decide +kernel

private theorem block233 : checkPow pointTest 238592 10 = true :=
  by decide +kernel

private theorem block234 : checkPow pointTest 239616 10 = true :=
  by decide +kernel

private theorem block235 : checkPow pointTest 240640 10 = true :=
  by decide +kernel

private theorem block236 : checkPow pointTest 241664 10 = true :=
  by decide +kernel

private theorem block237 : checkPow pointTest 242688 10 = true :=
  by decide +kernel

private theorem block238 : checkPow pointTest 243712 10 = true :=
  by decide +kernel

private theorem block239 : checkPow pointTest 244736 10 = true :=
  by decide +kernel

private theorem block240 : checkPow pointTest 245760 10 = true :=
  by decide +kernel

private theorem block241 : checkPow pointTest 246784 10 = true :=
  by decide +kernel

private theorem block242 : checkPow pointTest 247808 10 = true :=
  by decide +kernel

private theorem block243 : checkPow pointTest 248832 10 = true :=
  by decide +kernel

private theorem block244 : checkPow pointTest 249856 10 = true :=
  by decide +kernel

private theorem block245 : checkPow pointTest 250880 10 = true :=
  by decide +kernel

private theorem block246 : checkPow pointTest 251904 10 = true :=
  by decide +kernel

private theorem block247 : checkPow pointTest 252928 10 = true :=
  by decide +kernel

private theorem block248 : checkPow pointTest 253952 10 = true :=
  by decide +kernel

private theorem block249 : checkPow pointTest 254976 10 = true :=
  by decide +kernel

private theorem block250 : checkPow pointTest 256000 10 = true :=
  by decide +kernel

private theorem block251 : checkPow pointTest 257024 10 = true :=
  by decide +kernel

private theorem block252 : checkPow pointTest 258048 10 = true :=
  by decide +kernel

private theorem block253 : checkPow pointTest 259072 10 = true :=
  by decide +kernel

private theorem block254 : checkPow pointTest 260096 10 = true :=
  by decide +kernel

private theorem block255 : checkPow pointTest 261120 10 = true :=
  by decide +kernel

private theorem block256 : checkPow pointTest 262144 10 = true :=
  by decide +kernel

private theorem block257 : checkPow pointTest 263168 10 = true :=
  by decide +kernel

private theorem block258 : checkPow pointTest 264192 10 = true :=
  by decide +kernel

private theorem block259 : checkPow pointTest 265216 10 = true :=
  by decide +kernel

private theorem block260 : checkPow pointTest 266240 10 = true :=
  by decide +kernel

private theorem block261 : checkPow pointTest 267264 10 = true :=
  by decide +kernel

private theorem block262 : checkPow pointTest 268288 10 = true :=
  by decide +kernel

private theorem block263 : checkPow pointTest 269312 10 = true :=
  by decide +kernel

private theorem block264 : checkPow pointTest 270336 10 = true :=
  by decide +kernel

private theorem block265 : checkPow pointTest 271360 10 = true :=
  by decide +kernel

private theorem block266 : checkPow pointTest 272384 10 = true :=
  by decide +kernel

private theorem block267 : checkPow pointTest 273408 10 = true :=
  by decide +kernel

private theorem block268 : checkPow pointTest 274432 10 = true :=
  by decide +kernel

private theorem block269 : checkPow pointTest 275456 10 = true :=
  by decide +kernel

private theorem block270 : checkPow pointTest 276480 10 = true :=
  by decide +kernel

private theorem block271 : checkPow pointTest 277504 10 = true :=
  by decide +kernel

private theorem block272 : checkPow pointTest 278528 10 = true :=
  by decide +kernel

private theorem block273 : checkPow pointTest 279552 10 = true :=
  by decide +kernel

private theorem block274 : checkPow pointTest 280576 10 = true :=
  by decide +kernel

private theorem block275 : checkPow pointTest 281600 10 = true :=
  by decide +kernel

private theorem block276 : checkPow pointTest 282624 10 = true :=
  by decide +kernel

private theorem block277 : checkPow pointTest 283648 10 = true :=
  by decide +kernel

private theorem block278 : checkPow pointTest 284672 10 = true :=
  by decide +kernel

private theorem block279 : checkPow pointTest 285696 10 = true :=
  by decide +kernel

private theorem block280 : checkPow pointTest 286720 10 = true :=
  by decide +kernel

private theorem block281 : checkPow pointTest 287744 10 = true :=
  by decide +kernel

private theorem block282 : checkPow pointTest 288768 10 = true :=
  by decide +kernel

private theorem block283 : checkPow pointTest 289792 10 = true :=
  by decide +kernel

private theorem block284 : checkPow pointTest 290816 10 = true :=
  by decide +kernel

private theorem block285 : checkPow pointTest 291840 10 = true :=
  by decide +kernel

private theorem block286 : checkPow pointTest 292864 10 = true :=
  by decide +kernel

private theorem block287 : checkPow pointTest 293888 10 = true :=
  by decide +kernel

private theorem block288 : checkPow pointTest 294912 10 = true :=
  by decide +kernel

private theorem block289 : checkPow pointTest 295936 10 = true :=
  by decide +kernel

private theorem block290 : checkPow pointTest 296960 10 = true :=
  by decide +kernel

private theorem block291 : checkPow pointTest 297984 10 = true :=
  by decide +kernel

private theorem block292 : checkPow pointTest 299008 10 = true :=
  by decide +kernel

private theorem block293 : checkPow pointTest 300032 10 = true :=
  by decide +kernel

private theorem block294 : checkPow pointTest 301056 10 = true :=
  by decide +kernel

private theorem block295 : checkPow pointTest 302080 10 = true :=
  by decide +kernel

private theorem block296 : checkPow pointTest 303104 10 = true :=
  by decide +kernel

private theorem block297 : checkPow pointTest 304128 10 = true :=
  by decide +kernel

private theorem block298 : checkPow pointTest 305152 10 = true :=
  by decide +kernel

private theorem block299 : checkPow pointTest 306176 10 = true :=
  by decide +kernel

private theorem chunk0 : checkPow pointTest 0 18 = true :=
  (checkPow_join pointTest 17 0
  (checkPow_join pointTest 16 0
    (checkPow_join pointTest 15 0
      (checkPow_join pointTest 14 0
        (checkPow_join pointTest 13 0
          (checkPow_join pointTest 12 0
            (checkPow_join pointTest 11 0
              (checkPow_join pointTest 10 0
                block0
                block1)
              (checkPow_join pointTest 10 2048
                block2
                block3))
            (checkPow_join pointTest 11 4096
              (checkPow_join pointTest 10 4096
                block4
                block5)
              (checkPow_join pointTest 10 6144
                block6
                block7)))
          (checkPow_join pointTest 12 8192
            (checkPow_join pointTest 11 8192
              (checkPow_join pointTest 10 8192
                block8
                block9)
              (checkPow_join pointTest 10 10240
                block10
                block11))
            (checkPow_join pointTest 11 12288
              (checkPow_join pointTest 10 12288
                block12
                block13)
              (checkPow_join pointTest 10 14336
                block14
                block15))))
        (checkPow_join pointTest 13 16384
          (checkPow_join pointTest 12 16384
            (checkPow_join pointTest 11 16384
              (checkPow_join pointTest 10 16384
                block16
                block17)
              (checkPow_join pointTest 10 18432
                block18
                block19))
            (checkPow_join pointTest 11 20480
              (checkPow_join pointTest 10 20480
                block20
                block21)
              (checkPow_join pointTest 10 22528
                block22
                block23)))
          (checkPow_join pointTest 12 24576
            (checkPow_join pointTest 11 24576
              (checkPow_join pointTest 10 24576
                block24
                block25)
              (checkPow_join pointTest 10 26624
                block26
                block27))
            (checkPow_join pointTest 11 28672
              (checkPow_join pointTest 10 28672
                block28
                block29)
              (checkPow_join pointTest 10 30720
                block30
                block31)))))
      (checkPow_join pointTest 14 32768
        (checkPow_join pointTest 13 32768
          (checkPow_join pointTest 12 32768
            (checkPow_join pointTest 11 32768
              (checkPow_join pointTest 10 32768
                block32
                block33)
              (checkPow_join pointTest 10 34816
                block34
                block35))
            (checkPow_join pointTest 11 36864
              (checkPow_join pointTest 10 36864
                block36
                block37)
              (checkPow_join pointTest 10 38912
                block38
                block39)))
          (checkPow_join pointTest 12 40960
            (checkPow_join pointTest 11 40960
              (checkPow_join pointTest 10 40960
                block40
                block41)
              (checkPow_join pointTest 10 43008
                block42
                block43))
            (checkPow_join pointTest 11 45056
              (checkPow_join pointTest 10 45056
                block44
                block45)
              (checkPow_join pointTest 10 47104
                block46
                block47))))
        (checkPow_join pointTest 13 49152
          (checkPow_join pointTest 12 49152
            (checkPow_join pointTest 11 49152
              (checkPow_join pointTest 10 49152
                block48
                block49)
              (checkPow_join pointTest 10 51200
                block50
                block51))
            (checkPow_join pointTest 11 53248
              (checkPow_join pointTest 10 53248
                block52
                block53)
              (checkPow_join pointTest 10 55296
                block54
                block55)))
          (checkPow_join pointTest 12 57344
            (checkPow_join pointTest 11 57344
              (checkPow_join pointTest 10 57344
                block56
                block57)
              (checkPow_join pointTest 10 59392
                block58
                block59))
            (checkPow_join pointTest 11 61440
              (checkPow_join pointTest 10 61440
                block60
                block61)
              (checkPow_join pointTest 10 63488
                block62
                block63))))))
    (checkPow_join pointTest 15 65536
      (checkPow_join pointTest 14 65536
        (checkPow_join pointTest 13 65536
          (checkPow_join pointTest 12 65536
            (checkPow_join pointTest 11 65536
              (checkPow_join pointTest 10 65536
                block64
                block65)
              (checkPow_join pointTest 10 67584
                block66
                block67))
            (checkPow_join pointTest 11 69632
              (checkPow_join pointTest 10 69632
                block68
                block69)
              (checkPow_join pointTest 10 71680
                block70
                block71)))
          (checkPow_join pointTest 12 73728
            (checkPow_join pointTest 11 73728
              (checkPow_join pointTest 10 73728
                block72
                block73)
              (checkPow_join pointTest 10 75776
                block74
                block75))
            (checkPow_join pointTest 11 77824
              (checkPow_join pointTest 10 77824
                block76
                block77)
              (checkPow_join pointTest 10 79872
                block78
                block79))))
        (checkPow_join pointTest 13 81920
          (checkPow_join pointTest 12 81920
            (checkPow_join pointTest 11 81920
              (checkPow_join pointTest 10 81920
                block80
                block81)
              (checkPow_join pointTest 10 83968
                block82
                block83))
            (checkPow_join pointTest 11 86016
              (checkPow_join pointTest 10 86016
                block84
                block85)
              (checkPow_join pointTest 10 88064
                block86
                block87)))
          (checkPow_join pointTest 12 90112
            (checkPow_join pointTest 11 90112
              (checkPow_join pointTest 10 90112
                block88
                block89)
              (checkPow_join pointTest 10 92160
                block90
                block91))
            (checkPow_join pointTest 11 94208
              (checkPow_join pointTest 10 94208
                block92
                block93)
              (checkPow_join pointTest 10 96256
                block94
                block95)))))
      (checkPow_join pointTest 14 98304
        (checkPow_join pointTest 13 98304
          (checkPow_join pointTest 12 98304
            (checkPow_join pointTest 11 98304
              (checkPow_join pointTest 10 98304
                block96
                block97)
              (checkPow_join pointTest 10 100352
                block98
                block99))
            (checkPow_join pointTest 11 102400
              (checkPow_join pointTest 10 102400
                block100
                block101)
              (checkPow_join pointTest 10 104448
                block102
                block103)))
          (checkPow_join pointTest 12 106496
            (checkPow_join pointTest 11 106496
              (checkPow_join pointTest 10 106496
                block104
                block105)
              (checkPow_join pointTest 10 108544
                block106
                block107))
            (checkPow_join pointTest 11 110592
              (checkPow_join pointTest 10 110592
                block108
                block109)
              (checkPow_join pointTest 10 112640
                block110
                block111))))
        (checkPow_join pointTest 13 114688
          (checkPow_join pointTest 12 114688
            (checkPow_join pointTest 11 114688
              (checkPow_join pointTest 10 114688
                block112
                block113)
              (checkPow_join pointTest 10 116736
                block114
                block115))
            (checkPow_join pointTest 11 118784
              (checkPow_join pointTest 10 118784
                block116
                block117)
              (checkPow_join pointTest 10 120832
                block118
                block119)))
          (checkPow_join pointTest 12 122880
            (checkPow_join pointTest 11 122880
              (checkPow_join pointTest 10 122880
                block120
                block121)
              (checkPow_join pointTest 10 124928
                block122
                block123))
            (checkPow_join pointTest 11 126976
              (checkPow_join pointTest 10 126976
                block124
                block125)
              (checkPow_join pointTest 10 129024
                block126
                block127)))))))
  (checkPow_join pointTest 16 131072
    (checkPow_join pointTest 15 131072
      (checkPow_join pointTest 14 131072
        (checkPow_join pointTest 13 131072
          (checkPow_join pointTest 12 131072
            (checkPow_join pointTest 11 131072
              (checkPow_join pointTest 10 131072
                block128
                block129)
              (checkPow_join pointTest 10 133120
                block130
                block131))
            (checkPow_join pointTest 11 135168
              (checkPow_join pointTest 10 135168
                block132
                block133)
              (checkPow_join pointTest 10 137216
                block134
                block135)))
          (checkPow_join pointTest 12 139264
            (checkPow_join pointTest 11 139264
              (checkPow_join pointTest 10 139264
                block136
                block137)
              (checkPow_join pointTest 10 141312
                block138
                block139))
            (checkPow_join pointTest 11 143360
              (checkPow_join pointTest 10 143360
                block140
                block141)
              (checkPow_join pointTest 10 145408
                block142
                block143))))
        (checkPow_join pointTest 13 147456
          (checkPow_join pointTest 12 147456
            (checkPow_join pointTest 11 147456
              (checkPow_join pointTest 10 147456
                block144
                block145)
              (checkPow_join pointTest 10 149504
                block146
                block147))
            (checkPow_join pointTest 11 151552
              (checkPow_join pointTest 10 151552
                block148
                block149)
              (checkPow_join pointTest 10 153600
                block150
                block151)))
          (checkPow_join pointTest 12 155648
            (checkPow_join pointTest 11 155648
              (checkPow_join pointTest 10 155648
                block152
                block153)
              (checkPow_join pointTest 10 157696
                block154
                block155))
            (checkPow_join pointTest 11 159744
              (checkPow_join pointTest 10 159744
                block156
                block157)
              (checkPow_join pointTest 10 161792
                block158
                block159)))))
      (checkPow_join pointTest 14 163840
        (checkPow_join pointTest 13 163840
          (checkPow_join pointTest 12 163840
            (checkPow_join pointTest 11 163840
              (checkPow_join pointTest 10 163840
                block160
                block161)
              (checkPow_join pointTest 10 165888
                block162
                block163))
            (checkPow_join pointTest 11 167936
              (checkPow_join pointTest 10 167936
                block164
                block165)
              (checkPow_join pointTest 10 169984
                block166
                block167)))
          (checkPow_join pointTest 12 172032
            (checkPow_join pointTest 11 172032
              (checkPow_join pointTest 10 172032
                block168
                block169)
              (checkPow_join pointTest 10 174080
                block170
                block171))
            (checkPow_join pointTest 11 176128
              (checkPow_join pointTest 10 176128
                block172
                block173)
              (checkPow_join pointTest 10 178176
                block174
                block175))))
        (checkPow_join pointTest 13 180224
          (checkPow_join pointTest 12 180224
            (checkPow_join pointTest 11 180224
              (checkPow_join pointTest 10 180224
                block176
                block177)
              (checkPow_join pointTest 10 182272
                block178
                block179))
            (checkPow_join pointTest 11 184320
              (checkPow_join pointTest 10 184320
                block180
                block181)
              (checkPow_join pointTest 10 186368
                block182
                block183)))
          (checkPow_join pointTest 12 188416
            (checkPow_join pointTest 11 188416
              (checkPow_join pointTest 10 188416
                block184
                block185)
              (checkPow_join pointTest 10 190464
                block186
                block187))
            (checkPow_join pointTest 11 192512
              (checkPow_join pointTest 10 192512
                block188
                block189)
              (checkPow_join pointTest 10 194560
                block190
                block191))))))
    (checkPow_join pointTest 15 196608
      (checkPow_join pointTest 14 196608
        (checkPow_join pointTest 13 196608
          (checkPow_join pointTest 12 196608
            (checkPow_join pointTest 11 196608
              (checkPow_join pointTest 10 196608
                block192
                block193)
              (checkPow_join pointTest 10 198656
                block194
                block195))
            (checkPow_join pointTest 11 200704
              (checkPow_join pointTest 10 200704
                block196
                block197)
              (checkPow_join pointTest 10 202752
                block198
                block199)))
          (checkPow_join pointTest 12 204800
            (checkPow_join pointTest 11 204800
              (checkPow_join pointTest 10 204800
                block200
                block201)
              (checkPow_join pointTest 10 206848
                block202
                block203))
            (checkPow_join pointTest 11 208896
              (checkPow_join pointTest 10 208896
                block204
                block205)
              (checkPow_join pointTest 10 210944
                block206
                block207))))
        (checkPow_join pointTest 13 212992
          (checkPow_join pointTest 12 212992
            (checkPow_join pointTest 11 212992
              (checkPow_join pointTest 10 212992
                block208
                block209)
              (checkPow_join pointTest 10 215040
                block210
                block211))
            (checkPow_join pointTest 11 217088
              (checkPow_join pointTest 10 217088
                block212
                block213)
              (checkPow_join pointTest 10 219136
                block214
                block215)))
          (checkPow_join pointTest 12 221184
            (checkPow_join pointTest 11 221184
              (checkPow_join pointTest 10 221184
                block216
                block217)
              (checkPow_join pointTest 10 223232
                block218
                block219))
            (checkPow_join pointTest 11 225280
              (checkPow_join pointTest 10 225280
                block220
                block221)
              (checkPow_join pointTest 10 227328
                block222
                block223)))))
      (checkPow_join pointTest 14 229376
        (checkPow_join pointTest 13 229376
          (checkPow_join pointTest 12 229376
            (checkPow_join pointTest 11 229376
              (checkPow_join pointTest 10 229376
                block224
                block225)
              (checkPow_join pointTest 10 231424
                block226
                block227))
            (checkPow_join pointTest 11 233472
              (checkPow_join pointTest 10 233472
                block228
                block229)
              (checkPow_join pointTest 10 235520
                block230
                block231)))
          (checkPow_join pointTest 12 237568
            (checkPow_join pointTest 11 237568
              (checkPow_join pointTest 10 237568
                block232
                block233)
              (checkPow_join pointTest 10 239616
                block234
                block235))
            (checkPow_join pointTest 11 241664
              (checkPow_join pointTest 10 241664
                block236
                block237)
              (checkPow_join pointTest 10 243712
                block238
                block239))))
        (checkPow_join pointTest 13 245760
          (checkPow_join pointTest 12 245760
            (checkPow_join pointTest 11 245760
              (checkPow_join pointTest 10 245760
                block240
                block241)
              (checkPow_join pointTest 10 247808
                block242
                block243))
            (checkPow_join pointTest 11 249856
              (checkPow_join pointTest 10 249856
                block244
                block245)
              (checkPow_join pointTest 10 251904
                block246
                block247)))
          (checkPow_join pointTest 12 253952
            (checkPow_join pointTest 11 253952
              (checkPow_join pointTest 10 253952
                block248
                block249)
              (checkPow_join pointTest 10 256000
                block250
                block251))
            (checkPow_join pointTest 11 258048
              (checkPow_join pointTest 10 258048
                block252
                block253)
              (checkPow_join pointTest 10 260096
                block254
                block255))))))))

private theorem chunk1 : checkPow pointTest 262144 15 = true :=
  (checkPow_join pointTest 14 262144
  (checkPow_join pointTest 13 262144
    (checkPow_join pointTest 12 262144
      (checkPow_join pointTest 11 262144
        (checkPow_join pointTest 10 262144
          block256
          block257)
        (checkPow_join pointTest 10 264192
          block258
          block259))
      (checkPow_join pointTest 11 266240
        (checkPow_join pointTest 10 266240
          block260
          block261)
        (checkPow_join pointTest 10 268288
          block262
          block263)))
    (checkPow_join pointTest 12 270336
      (checkPow_join pointTest 11 270336
        (checkPow_join pointTest 10 270336
          block264
          block265)
        (checkPow_join pointTest 10 272384
          block266
          block267))
      (checkPow_join pointTest 11 274432
        (checkPow_join pointTest 10 274432
          block268
          block269)
        (checkPow_join pointTest 10 276480
          block270
          block271))))
  (checkPow_join pointTest 13 278528
    (checkPow_join pointTest 12 278528
      (checkPow_join pointTest 11 278528
        (checkPow_join pointTest 10 278528
          block272
          block273)
        (checkPow_join pointTest 10 280576
          block274
          block275))
      (checkPow_join pointTest 11 282624
        (checkPow_join pointTest 10 282624
          block276
          block277)
        (checkPow_join pointTest 10 284672
          block278
          block279)))
    (checkPow_join pointTest 12 286720
      (checkPow_join pointTest 11 286720
        (checkPow_join pointTest 10 286720
          block280
          block281)
        (checkPow_join pointTest 10 288768
          block282
          block283))
      (checkPow_join pointTest 11 290816
        (checkPow_join pointTest 10 290816
          block284
          block285)
        (checkPow_join pointTest 10 292864
          block286
          block287)))))

private theorem chunk2 : checkPow pointTest 294912 13 = true :=
  (checkPow_join pointTest 12 294912
  (checkPow_join pointTest 11 294912
    (checkPow_join pointTest 10 294912
      block288
      block289)
    (checkPow_join pointTest 10 296960
      block290
      block291))
  (checkPow_join pointTest 11 299008
    (checkPow_join pointTest 10 299008
      block292
      block293)
    (checkPow_join pointTest 10 301056
      block294
      block295)))

private theorem chunk3 : checkPow pointTest 303104 12 = true :=
  (checkPow_join pointTest 11 303104
  (checkPow_join pointTest 10 303104
    block296
    block297)
  (checkPow_join pointTest 10 305152
    block298
    block299))

/-- The packed inverse cancels the forward map on every ambient point. -/
theorem bMap_left_inv (x : Fin 306936) : bInvMap (bMap x) = x :=
  leftInverse_of_checks bMap bInvMap chunk0 chunk1 chunk2 chunk3 x

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks
