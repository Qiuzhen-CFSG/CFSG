module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data

/-!
# Witnesses for the first cubic centralizer in the Hall--Janko carrier

The tables contain 1080 proposed centralizer elements and their carrier fusion
conjugators, and 560 proposed conjugates with right-coset representatives.
Balanced lookup trees also decode each enumerated normal form to its row.
`Checks` verifies all equations and both decoding identities. No external
centralizer size, orbit completeness, or conjugacy assertion is assumed.

Source: retained ATLAS `J2G1-p100B0` data. See `source/README.md` for attribution
and the witness discovery and emission scripts.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate.OneCentralizerCertificates
open GeneratorPair.SecondOrbitCertificate

/-- Encode the existing four transversal indices in mixed radix. -/
def indexCode (i : Index) : Nat :=
  i.1.val + 100 * (i.2.1.val + 63 * (i.2.2.1.val + 24 * i.2.2.2.val))

/-- Decode a mixed-radix normal-form index. -/
def indexOfCode (n : Nat) : Index :=
  (⟨n % 100, Nat.mod_lt _ (by decide)⟩,
   ⟨n / 100 % 63, Nat.mod_lt _ (by decide)⟩,
   ⟨n / 6300 % 24, Nat.mod_lt _ (by decide)⟩,
   ⟨n / 151200 % 4, Nat.mod_lt _ (by decide)⟩)

def centralCode (i : Fin 1080) : Nat :=
 (if i.val < 540 then
 (if i.val < 270 then
 (if i.val < 135 then
 (if i.val < 67 then
 (if i.val < 33 then
 (if i.val < 16 then
 (if i.val < 8 then
 (if i.val < 4 then
 (if i.val < 2 then
 (if i.val < 1 then
 0 else
 4238430537880) else
 (if i.val < 3 then
 4206744461434 else
 189137896508)) else
 (if i.val < 6 then
 (if i.val < 5 then
 2076635839629 else
 4820269308840) else
 (if i.val < 7 then
 4261884685899 else
 4525051309903))) else
 (if i.val < 12 then
 (if i.val < 10 then
 (if i.val < 9 then
 7405293374008 else
 464656353525) else
 (if i.val < 11 then
 2694958565883 else
 2405027727699)) else
 (if i.val < 14 then
 (if i.val < 13 then
 6457913489450 else
 3747959518666) else
 (if i.val < 15 then
 7172582064019 else
 4793232337847)))) else
 (if i.val < 24 then
 (if i.val < 20 then
 (if i.val < 18 then
 (if i.val < 17 then
 375082457773 else
 3481291714326) else
 (if i.val < 19 then
 6608168194691 else
 6812472054192)) else
 (if i.val < 22 then
 (if i.val < 21 then
 3996958711529 else
 331342721510) else
 (if i.val < 23 then
 7435719060711 else
 2581524709412))) else
 (if i.val < 28 then
 (if i.val < 26 then
 (if i.val < 25 then
 4571020357677 else
 7040318361805) else
 (if i.val < 27 then
 5743509227697 else
 5182991475287)) else
 (if i.val < 30 then
 (if i.val < 29 then
 6660644883633 else
 5745369595236) else
 (if i.val < 31 then
 4186249022771 else
 (if i.val < 32 then
 6523071634484 else
 2402231151740)))))) else
 (if i.val < 50 then
 (if i.val < 41 then
 (if i.val < 37 then
 (if i.val < 35 then
 (if i.val < 34 then
 1608230358448 else
 1701847955685) else
 (if i.val < 36 then
 4776267108648 else
 3935770501580)) else
 (if i.val < 39 then
 (if i.val < 38 then
 7012065139841 else
 3413330352777) else
 (if i.val < 40 then
 3699236247247 else
 2582309751603))) else
 (if i.val < 45 then
 (if i.val < 43 then
 (if i.val < 42 then
 2419418968167 else
 255226840267) else
 (if i.val < 44 then
 4035364735373 else
 2828761519880)) else
 (if i.val < 47 then
 (if i.val < 46 then
 1659070458166 else
 3621078551047) else
 (if i.val < 48 then
 5840378240700 else
 (if i.val < 49 then
 3875202810510 else
 621047984911))))) else
 (if i.val < 58 then
 (if i.val < 54 then
 (if i.val < 52 then
 (if i.val < 51 then
 314812948836 else
 5442310978050) else
 (if i.val < 53 then
 4460017196928 else
 1413831923885)) else
 (if i.val < 56 then
 (if i.val < 55 then
 6136165361040 else
 7009371367841) else
 (if i.val < 57 then
 2581039679025 else
 3442026911463))) else
 (if i.val < 62 then
 (if i.val < 60 then
 (if i.val < 59 then
 231308822179 else
 863010931092) else
 (if i.val < 61 then
 5200980662419 else
 6031563390205)) else
 (if i.val < 64 then
 (if i.val < 63 then
 40866981727 else
 4424565641348) else
 (if i.val < 65 then
 6495096022256 else
 (if i.val < 66 then
 6150586823371 else
 4204178942497))))))) else
 (if i.val < 101 then
 (if i.val < 84 then
 (if i.val < 75 then
 (if i.val < 71 then
 (if i.val < 69 then
 (if i.val < 68 then
 5951419532363 else
 648397052519) else
 (if i.val < 70 then
 6706229891487 else
 2719040531579)) else
 (if i.val < 73 then
 (if i.val < 72 then
 635216042092 else
 6326322353008) else
 (if i.val < 74 then
 4505020376329 else
 2560536363628))) else
 (if i.val < 79 then
 (if i.val < 77 then
 (if i.val < 76 then
 3871003093733 else
 2504206502405) else
 (if i.val < 78 then
 2015409561829 else
 2331144192983)) else
 (if i.val < 81 then
 (if i.val < 80 then
 1423992578780 else
 1880929261066) else
 (if i.val < 82 then
 6319814105947 else
 (if i.val < 83 then
 7215012454800 else
 2790008375010))))) else
 (if i.val < 92 then
 (if i.val < 88 then
 (if i.val < 86 then
 (if i.val < 85 then
 6849081843811 else
 2143998513336) else
 (if i.val < 87 then
 1754213380950 else
 1244206105428)) else
 (if i.val < 90 then
 (if i.val < 89 then
 3250200093185 else
 3101488845540) else
 (if i.val < 91 then
 2570693988341 else
 5883262817925))) else
 (if i.val < 96 then
 (if i.val < 94 then
 (if i.val < 93 then
 3490057122579 else
 273007986999) else
 (if i.val < 95 then
 870007881671 else
 7262638041792)) else
 (if i.val < 98 then
 (if i.val < 97 then
 987137078663 else
 4926070052644) else
 (if i.val < 99 then
 1924340603464 else
 (if i.val < 100 then
 6951202937761 else
 4255510152640)))))) else
 (if i.val < 118 then
 (if i.val < 109 then
 (if i.val < 105 then
 (if i.val < 103 then
 (if i.val < 102 then
 1063073958548 else
 6233846032726) else
 (if i.val < 104 then
 4658059591680 else
 5833729102652)) else
 (if i.val < 107 then
 (if i.val < 106 then
 7138486520671 else
 3628673663548) else
 (if i.val < 108 then
 1760271676761 else
 5975681107366))) else
 (if i.val < 113 then
 (if i.val < 111 then
 (if i.val < 110 then
 7589219165010 else
 3968799878611) else
 (if i.val < 112 then
 4836748359700 else
 4650208686573)) else
 (if i.val < 115 then
 (if i.val < 114 then
 657721279010 else
 3380028895011) else
 (if i.val < 116 then
 1970635029626 else
 (if i.val < 117 then
 2328994754562 else
 5475482480127))))) else
 (if i.val < 126 then
 (if i.val < 122 then
 (if i.val < 120 then
 (if i.val < 119 then
 5565939392427 else
 6046448761526) else
 (if i.val < 121 then
 5019156045340 else
 1683622356585)) else
 (if i.val < 124 then
 (if i.val < 123 then
 6615619390283 else
 2796515441947) else
 (if i.val < 125 then
 468225954083 else
 7212236446984))) else
 (if i.val < 130 then
 (if i.val < 128 then
 (if i.val < 127 then
 1235993547845 else
 5635512566320) else
 (if i.val < 129 then
 2867323008962 else
 4635739460333)) else
 (if i.val < 132 then
 (if i.val < 131 then
 4716877009525 else
 7155819496629) else
 (if i.val < 133 then
 7151619161097 else
 (if i.val < 134 then
 6998461423734 else
 6685576611361)))))))) else
 (if i.val < 202 then
 (if i.val < 168 then
 (if i.val < 151 then
 (if i.val < 143 then
 (if i.val < 139 then
 (if i.val < 137 then
 (if i.val < 136 then
 7451561859473 else
 42989869100) else
 (if i.val < 138 then
 1579075424608 else
 5627651380228)) else
 (if i.val < 141 then
 (if i.val < 140 then
 7413802986756 else
 1160856225262) else
 (if i.val < 142 then
 5467629163303 else
 2848996968567))) else
 (if i.val < 147 then
 (if i.val < 145 then
 (if i.val < 144 then
 4501400684348 else
 1668100777367) else
 (if i.val < 146 then
 1912014803067 else
 914474617791)) else
 (if i.val < 149 then
 (if i.val < 148 then
 3215751923433 else
 1229123028552) else
 (if i.val < 150 then
 5909534150052 else
 2083513708764)))) else
 (if i.val < 159 then
 (if i.val < 155 then
 (if i.val < 153 then
 (if i.val < 152 then
 6488103369787 else
 5305205895077) else
 (if i.val < 154 then
 4385081319350 else
 2750963732550)) else
 (if i.val < 157 then
 (if i.val < 156 then
 3222646043471 else
 2476633710708) else
 (if i.val < 158 then
 5280264550097 else
 2082731101679))) else
 (if i.val < 163 then
 (if i.val < 161 then
 (if i.val < 160 then
 2031269880200 else
 374608373205) else
 (if i.val < 162 then
 1768279253320 else
 4686431997992)) else
 (if i.val < 165 then
 (if i.val < 164 then
 415318673263 else
 431292046233) else
 (if i.val < 166 then
 5363075585564 else
 (if i.val < 167 then
 6723602821234 else
 7539980610361)))))) else
 (if i.val < 185 then
 (if i.val < 176 then
 (if i.val < 172 then
 (if i.val < 170 then
 (if i.val < 169 then
 5401857782083 else
 7451562480380) else
 (if i.val < 171 then
 3121291 else
 2669661687825)) else
 (if i.val < 174 then
 (if i.val < 173 then
 4523797653185 else
 7087298094845) else
 (if i.val < 175 then
 55987039084 else
 2455482050734))) else
 (if i.val < 180 then
 (if i.val < 178 then
 (if i.val < 177 then
 158141994329 else
 2215868759440) else
 (if i.val < 179 then
 1600279732552 else
 6169429425520)) else
 (if i.val < 182 then
 (if i.val < 181 then
 2140087320179 else
 579703925299) else
 (if i.val < 183 then
 4152594398992 else
 (if i.val < 184 then
 6609456504663 else
 3211208079644))))) else
 (if i.val < 193 then
 (if i.val < 189 then
 (if i.val < 187 then
 (if i.val < 186 then
 5323898464045 else
 4579745286950) else
 (if i.val < 188 then
 3751870250264 else
 6261940241085)) else
 (if i.val < 191 then
 (if i.val < 190 then
 3755743391164 else
 3137597270420) else
 (if i.val < 192 then
 2860986547703 else
 1493768411185))) else
 (if i.val < 197 then
 (if i.val < 195 then
 (if i.val < 194 then
 5826721931683 else
 7434900252450) else
 (if i.val < 196 then
 4984338349484 else
 1347603978728)) else
 (if i.val < 199 then
 (if i.val < 198 then
 5761085409462 else
 7151620402334) else
 (if i.val < 200 then
 1092931167536 else
 (if i.val < 201 then
 2683989414661 else
 3659930378066))))))) else
 (if i.val < 236 then
 (if i.val < 219 then
 (if i.val < 210 then
 (if i.val < 206 then
 (if i.val < 204 then
 (if i.val < 203 then
 388227282256 else
 1105387026677) else
 (if i.val < 205 then
 7157781505136 else
 1062908900547)) else
 (if i.val < 208 then
 (if i.val < 207 then
 5835812689528 else
 3404960008812) else
 (if i.val < 209 then
 525163682877 else
 2082730524625))) else
 (if i.val < 214 then
 (if i.val < 212 then
 (if i.val < 211 then
 5802242057926 else
 6314429034203) else
 (if i.val < 213 then
 1804240084266 else
 132575303826)) else
 (if i.val < 216 then
 (if i.val < 215 then
 2604544708727 else
 6288994776152) else
 (if i.val < 217 then
 2456933592262 else
 (if i.val < 218 then
 5362730875673 else
 947807602805))))) else
 (if i.val < 227 then
 (if i.val < 223 then
 (if i.val < 221 then
 (if i.val < 220 then
 1248287968510 else
 5009318416511) else
 (if i.val < 222 then
 7470380255484 else
 6344676299471)) else
 (if i.val < 225 then
 (if i.val < 224 then
 7011995685544 else
 3467043343461) else
 (if i.val < 226 then
 41159187020 else
 4403109238808))) else
 (if i.val < 231 then
 (if i.val < 229 then
 (if i.val < 228 then
 5401653392877 else
 7426413719636) else
 (if i.val < 230 then
 3024583157191 else
 5401207051727)) else
 (if i.val < 233 then
 (if i.val < 232 then
 475329385027 else
 5975578355120) else
 (if i.val < 234 then
 6484497596912 else
 (if i.val < 235 then
 2344775257812 else
 319880062700)))))) else
 (if i.val < 253 then
 (if i.val < 244 then
 (if i.val < 240 then
 (if i.val < 238 then
 (if i.val < 237 then
 2837826968505 else
 4963826581787) else
 (if i.val < 239 then
 1950642221510 else
 2719041226311)) else
 (if i.val < 242 then
 (if i.val < 241 then
 519814244062 else
 3219504759467) else
 (if i.val < 243 then
 1741728577297 else
 3340630475544))) else
 (if i.val < 248 then
 (if i.val < 246 then
 (if i.val < 245 then
 4339296195741 else
 3974297581545) else
 (if i.val < 247 then
 563324164084 else
 3697010088071)) else
 (if i.val < 250 then
 (if i.val < 249 then
 3177236501344 else
 3250206831261) else
 (if i.val < 251 then
 74786684420 else
 (if i.val < 252 then
 1350302627408 else
 1631235856677))))) else
 (if i.val < 261 then
 (if i.val < 257 then
 (if i.val < 255 then
 (if i.val < 254 then
 1480251165836 else
 1804000606591) else
 (if i.val < 256 then
 7068632197127 else
 316049269627)) else
 (if i.val < 259 then
 (if i.val < 258 then
 7206216335720 else
 3795047567912) else
 (if i.val < 260 then
 3095951385612 else
 460278952541))) else
 (if i.val < 265 then
 (if i.val < 263 then
 (if i.val < 262 then
 2796516117525 else
 2730168348064) else
 (if i.val < 264 then
 480901424836 else
 6755876212291)) else
 (if i.val < 267 then
 (if i.val < 266 then
 4562829077844 else
 7151619836341) else
 (if i.val < 268 then
 5255589375787 else
 (if i.val < 269 then
 7565322995079 else
 4150624614363))))))))) else
 (if i.val < 405 then
 (if i.val < 337 then
 (if i.val < 303 then
 (if i.val < 286 then
 (if i.val < 278 then
 (if i.val < 274 then
 (if i.val < 272 then
 (if i.val < 271 then
 963300793652 else
 534298615285) else
 (if i.val < 273 then
 4872181255783 else
 3968799358950)) else
 (if i.val < 276 then
 (if i.val < 275 then
 3402164659184 else
 6975777264428) else
 (if i.val < 277 then
 1333880506362 else
 5821096734434))) else
 (if i.val < 282 then
 (if i.val < 280 then
 (if i.val < 279 then
 3376226603636 else
 6175727868361) else
 (if i.val < 281 then
 7011983014166 else
 1293707879434)) else
 (if i.val < 284 then
 (if i.val < 283 then
 5504288586961 else
 5333699304283) else
 (if i.val < 285 then
 7567795426580 else
 2889023315491)))) else
 (if i.val < 294 then
 (if i.val < 290 then
 (if i.val < 288 then
 (if i.val < 287 then
 2712844470825 else
 3088959914585) else
 (if i.val < 289 then
 4634373905045 else
 7081141898884)) else
 (if i.val < 292 then
 (if i.val < 291 then
 3413471403334 else
 4980286847729) else
 (if i.val < 293 then
 1250897721640 else
 3396991814752))) else
 (if i.val < 298 then
 (if i.val < 296 then
 (if i.val < 295 then
 4374687302920 else
 3688158259883) else
 (if i.val < 297 then
 5714752339984 else
 3394877434445)) else
 (if i.val < 300 then
 (if i.val < 299 then
 2455474254520 else
 962520617162) else
 (if i.val < 301 then
 1758860777333 else
 (if i.val < 302 then
 1372763715325 else
 5492586320829)))))) else
 (if i.val < 320 then
 (if i.val < 311 then
 (if i.val < 307 then
 (if i.val < 305 then
 (if i.val < 304 then
 1987882814097 else
 7300723012734) else
 (if i.val < 306 then
 1163458766761 else
 4743245170073)) else
 (if i.val < 309 then
 (if i.val < 308 then
 2190944414900 else
 1314353343208) else
 (if i.val < 310 then
 2558751721228 else
 92669439756))) else
 (if i.val < 315 then
 (if i.val < 313 then
 (if i.val < 312 then
 2999543871862 else
 7284254310703) else
 (if i.val < 314 then
 7428852314140 else
 900088932848)) else
 (if i.val < 317 then
 (if i.val < 316 then
 4205188482226 else
 1390537583580) else
 (if i.val < 318 then
 6997076524952 else
 (if i.val < 319 then
 5061953002171 else
 7422889594648))))) else
 (if i.val < 328 then
 (if i.val < 324 then
 (if i.val < 322 then
 (if i.val < 321 then
 6313436612661 else
 6925125284866) else
 (if i.val < 323 then
 7262637553710 else
 5283384798511)) else
 (if i.val < 326 then
 (if i.val < 325 then
 2872939279600 else
 5853880544073) else
 (if i.val < 327 then
 2669470045263 else
 6505582784779))) else
 (if i.val < 332 then
 (if i.val < 330 then
 (if i.val < 329 then
 6633536692092 else
 870007396219) else
 (if i.val < 331 then
 1906445295205 else
 4060448358727)) else
 (if i.val < 334 then
 (if i.val < 333 then
 4122967744748 else
 924494436056) else
 (if i.val < 335 then
 2294466229171 else
 (if i.val < 336 then
 3088591007497 else
 5086433501773))))))) else
 (if i.val < 371 then
 (if i.val < 354 then
 (if i.val < 345 then
 (if i.val < 341 then
 (if i.val < 339 then
 (if i.val < 338 then
 7665455531556 else
 3270317685256) else
 (if i.val < 340 then
 4899018683803 else
 1112276978980)) else
 (if i.val < 343 then
 (if i.val < 342 then
 2138330461012 else
 1876785911819) else
 (if i.val < 344 then
 5401652846845 else
 4639401635540))) else
 (if i.val < 349 then
 (if i.val < 347 then
 (if i.val < 346 then
 1367110067848 else
 3336612842685) else
 (if i.val < 348 then
 3891968024448 else
 4552998700580)) else
 (if i.val < 351 then
 (if i.val < 350 then
 2499434170841 else
 7661886010977) else
 (if i.val < 352 then
 2160633073447 else
 (if i.val < 353 then
 6791355035403 else
 3361709023167))))) else
 (if i.val < 362 then
 (if i.val < 358 then
 (if i.val < 356 then
 (if i.val < 355 then
 6631090293667 else
 6568134243173) else
 (if i.val < 357 then
 4571021139479 else
 1693082154199)) else
 (if i.val < 360 then
 (if i.val < 359 then
 655364499892 else
 6245997805563) else
 (if i.val < 361 then
 4105665038144 else
 1699092052945))) else
 (if i.val < 366 then
 (if i.val < 364 then
 (if i.val < 363 then
 4315226424650 else
 6496311221564) else
 (if i.val < 365 then
 6150589397985 else
 6998460938464)) else
 (if i.val < 368 then
 (if i.val < 367 then
 5818158660920 else
 752653842203) else
 (if i.val < 369 then
 7611644679073 else
 (if i.val < 370 then
 1591180014456 else
 6921939227356)))))) else
 (if i.val < 388 then
 (if i.val < 379 then
 (if i.val < 375 then
 (if i.val < 373 then
 (if i.val < 372 then
 6476458667503 else
 1755176978680) else
 (if i.val < 374 then
 6295217647912 else
 7005572788319)) else
 (if i.val < 377 then
 (if i.val < 376 then
 3871003857745 else
 2947264394300) else
 (if i.val < 378 then
 10971280905 else
 7544531239787))) else
 (if i.val < 383 then
 (if i.val < 381 then
 (if i.val < 380 then
 2286104293910 else
 3412232821911) else
 (if i.val < 382 then
 6534426335662 else
 6280891151867)) else
 (if i.val < 385 then
 (if i.val < 384 then
 5296579756897 else
 7268155786344) else
 (if i.val < 386 then
 3871009308141 else
 (if i.val < 387 then
 6326330383545 else
 2505276559684))))) else
 (if i.val < 396 then
 (if i.val < 392 then
 (if i.val < 390 then
 (if i.val < 389 then
 5516074985905 else
 6240554021397) else
 (if i.val < 391 then
 1003313824187 else
 4003092189333)) else
 (if i.val < 394 then
 (if i.val < 393 then
 3520527713736 else
 6476458078871) else
 (if i.val < 395 then
 7173263884184 else
 7573832602156))) else
 (if i.val < 400 then
 (if i.val < 398 then
 (if i.val < 397 then
 4101067373777 else
 1075698713036) else
 (if i.val < 399 then
 1214694454047 else
 863563299028)) else
 (if i.val < 402 then
 (if i.val < 401 then
 3435615008712 else
 5930814177177) else
 (if i.val < 403 then
 2394873959725 else
 (if i.val < 404 then
 3949633925026 else
 475330690103)))))))) else
 (if i.val < 472 then
 (if i.val < 438 then
 (if i.val < 421 then
 (if i.val < 413 then
 (if i.val < 409 then
 (if i.val < 407 then
 (if i.val < 406 then
 1908400056966 else
 5154364076773) else
 (if i.val < 408 then
 3961199518926 else
 1067633711291)) else
 (if i.val < 411 then
 (if i.val < 410 then
 924481785192 else
 7128195408929) else
 (if i.val < 412 then
 951275636510 else
 3604231441311))) else
 (if i.val < 417 then
 (if i.val < 415 then
 (if i.val < 414 then
 3404947422812 else
 923071394277) else
 (if i.val < 416 then
 5200980253541 else
 527919872925)) else
 (if i.val < 419 then
 (if i.val < 418 then
 6863924423464 else
 1384160031436) else
 (if i.val < 420 then
 78215996491 else
 1306262398044)))) else
 (if i.val < 429 then
 (if i.val < 425 then
 (if i.val < 423 then
 (if i.val < 422 then
 6780960382141 else
 4171727988787) else
 (if i.val < 424 then
 4366463307279 else
 3549152916963)) else
 (if i.val < 427 then
 (if i.val < 426 then
 2248095665852 else
 7617192546726) else
 (if i.val < 428 then
 3481292543627 else
 1374554601452))) else
 (if i.val < 433 then
 (if i.val < 431 then
 (if i.val < 430 then
 1781978726362 else
 415319424173) else
 (if i.val < 432 then
 5749108685705 else
 3340631185810)) else
 (if i.val < 435 then
 (if i.val < 434 then
 4624213345811 else
 2386329363984) else
 (if i.val < 436 then
 1328711373650 else
 (if i.val < 437 then
 2650659626866 else
 4065439842619)))))) else
 (if i.val < 455 then
 (if i.val < 446 then
 (if i.val < 442 then
 (if i.val < 440 then
 (if i.val < 439 then
 5668649732447 else
 4716876578663) else
 (if i.val < 441 then
 6056990604419 else
 1665340035387)) else
 (if i.val < 444 then
 (if i.val < 443 then
 2530814278679 else
 4133617136392) else
 (if i.val < 445 then
 4716885047308 else
 859429))) else
 (if i.val < 450 then
 (if i.val < 448 then
 (if i.val < 447 then
 4573853477128 else
 7544482901633) else
 (if i.val < 449 then
 6312021462305 else
 1561339235329)) else
 (if i.val < 452 then
 (if i.val < 451 then
 1425340279283 else
 4007412920700) else
 (if i.val < 453 then
 2069339788180 else
 (if i.val < 454 then
 2236279103734 else
 5136411226808))))) else
 (if i.val < 463 then
 (if i.val < 459 then
 (if i.val < 457 then
 (if i.val < 456 then
 3021696577929 else
 1690479765540) else
 (if i.val < 458 then
 1520211027399 else
 573553875403)) else
 (if i.val < 461 then
 (if i.val < 460 then
 2668391773108 else
 2048438509425) else
 (if i.val < 462 then
 7102543454583 else
 4014988046799))) else
 (if i.val < 467 then
 (if i.val < 465 then
 (if i.val < 464 then
 2653500389510 else
 4200500165511) else
 (if i.val < 466 then
 653549564126 else
 5967664681062)) else
 (if i.val < 469 then
 (if i.val < 468 then
 468218281827 else
 1646808976527) else
 (if i.val < 470 then
 4345592899226 else
 (if i.val < 471 then
 753008323840 else
 1303989591885))))))) else
 (if i.val < 506 then
 (if i.val < 489 then
 (if i.val < 480 then
 (if i.val < 476 then
 (if i.val < 474 then
 (if i.val < 473 then
 1668108827183 else
 190336878847) else
 (if i.val < 475 then
 5821097454971 else
 3469327816608)) else
 (if i.val < 478 then
 (if i.val < 477 then
 2152345577597 else
 6471734039579) else
 (if i.val < 479 then
 5658490325300 else
 1433207535105))) else
 (if i.val < 484 then
 (if i.val < 482 then
 (if i.val < 481 then
 6882676287220 else
 239527083092) else
 (if i.val < 483 then
 6723603607963 else
 5639407073733)) else
 (if i.val < 486 then
 (if i.val < 485 then
 3280619941064 else
 7291737003866) else
 (if i.val < 487 then
 7561981602587 else
 (if i.val < 488 then
 3534840364233 else
 7640416300647))))) else
 (if i.val < 497 then
 (if i.val < 493 then
 (if i.val < 491 then
 (if i.val < 490 then
 4831209206544 else
 6456907373199) else
 (if i.val < 492 then
 1829408995734 else
 6697752039241)) else
 (if i.val < 495 then
 (if i.val < 494 then
 7284255024919 else
 5676104526697) else
 (if i.val < 496 then
 2352496284028 else
 1214702978999))) else
 (if i.val < 501 then
 (if i.val < 499 then
 (if i.val < 498 then
 5159806121545 else
 2216438057691) else
 (if i.val < 500 then
 989003110756 else
 3943221892419)) else
 (if i.val < 503 then
 (if i.val < 502 then
 5924654952112 else
 3253054373379) else
 (if i.val < 504 then
 6197518335399 else
 (if i.val < 505 then
 1269538383671 else
 5018027094192)))))) else
 (if i.val < 523 then
 (if i.val < 514 then
 (if i.val < 510 then
 (if i.val < 508 then
 (if i.val < 507 then
 3781782025463 else
 3186546333844) else
 (if i.val < 509 then
 19930865464 else
 2959986441361)) else
 (if i.val < 512 then
 (if i.val < 511 then
 1819100190866 else
 7588882514387) else
 (if i.val < 513 then
 700333288833 else
 2230263190047))) else
 (if i.val < 518 then
 (if i.val < 516 then
 (if i.val < 515 then
 4598479155144 else
 1160473596999) else
 (if i.val < 517 then
 4639402342734 else
 3779654951041)) else
 (if i.val < 520 then
 (if i.val < 519 then
 6000037232719 else
 3380028513697) else
 (if i.val < 521 then
 723414879028 else
 (if i.val < 522 then
 4951434389999 else
 2140088118145))))) else
 (if i.val < 531 then
 (if i.val < 527 then
 (if i.val < 525 then
 (if i.val < 524 then
 4107060409491 else
 532504316956) else
 (if i.val < 526 then
 2714683802619 else
 6135015895912)) else
 (if i.val < 529 then
 (if i.val < 528 then
 240746379567 else
 2340994818548) else
 (if i.val < 530 then
 1884978037967 else
 6490107282867))) else
 (if i.val < 535 then
 (if i.val < 533 then
 (if i.val < 532 then
 2288248396791 else
 4205442624033) else
 (if i.val < 534 then
 4186478516352 else
 5952952351452)) else
 (if i.val < 537 then
 (if i.val < 536 then
 2678361938964 else
 6007544019187) else
 (if i.val < 538 then
 3316549318877 else
 (if i.val < 539 then
 2424534637550 else
 3450786493950)))))))))) else
 (if i.val < 810 then
 (if i.val < 675 then
 (if i.val < 607 then
 (if i.val < 573 then
 (if i.val < 556 then
 (if i.val < 548 then
 (if i.val < 544 then
 (if i.val < 542 then
 (if i.val < 541 then
 4024025611285 else
 3495467909383) else
 (if i.val < 543 then
 5241844844550 else
 1193784784784)) else
 (if i.val < 546 then
 (if i.val < 545 then
 6631103710028 else
 5695891793562) else
 (if i.val < 547 then
 2794231343234 else
 4122970290836))) else
 (if i.val < 552 then
 (if i.val < 550 then
 (if i.val < 549 then
 6807861955561 else
 380406202166) else
 (if i.val < 551 then
 4782172053034 else
 5275262469361)) else
 (if i.val < 554 then
 (if i.val < 553 then
 6156875801083 else
 4150624169780) else
 (if i.val < 555 then
 6921938730691 else
 1003418548425)))) else
 (if i.val < 564 then
 (if i.val < 560 then
 (if i.val < 558 then
 (if i.val < 557 then
 2871700180985 else
 560782968245) else
 (if i.val < 559 then
 4863287227684 else
 6002764296934)) else
 (if i.val < 562 then
 (if i.val < 561 then
 6905111987729 else
 3273699252040) else
 (if i.val < 563 then
 6661174375552 else
 4721685406120))) else
 (if i.val < 568 then
 (if i.val < 566 then
 (if i.val < 565 then
 43764852683 else
 6469354193584) else
 (if i.val < 567 then
 1924149137645 else
 7212234268120)) else
 (if i.val < 570 then
 (if i.val < 569 then
 5786971661162 else
 7009371043733) else
 (if i.val < 571 then
 4397002762525 else
 (if i.val < 572 then
 7038182507229 else
 4142430952497)))))) else
 (if i.val < 590 then
 (if i.val < 581 then
 (if i.val < 577 then
 (if i.val < 575 then
 (if i.val < 574 then
 1858447298334 else
 4705663653961) else
 (if i.val < 576 then
 2910848287673 else
 365063647700)) else
 (if i.val < 579 then
 (if i.val < 578 then
 3751878329608 else
 2816176525228) else
 (if i.val < 580 then
 652309174956 else
 3098794727062))) else
 (if i.val < 585 then
 (if i.val < 583 then
 (if i.val < 582 then
 3922805092303 else
 3860219178940) else
 (if i.val < 584 then
 5762116200848 else
 4958347283026)) else
 (if i.val < 587 then
 (if i.val < 586 then
 1962976701180 else
 2075618887352) else
 (if i.val < 588 then
 2565169409371 else
 (if i.val < 589 then
 996991957048 else
 4003091691861))))) else
 (if i.val < 598 then
 (if i.val < 594 then
 (if i.val < 592 then
 (if i.val < 591 then
 6373631903266 else
 5805387829710) else
 (if i.val < 593 then
 7413802626511 else
 6965605910800)) else
 (if i.val < 596 then
 (if i.val < 595 then
 1336357335273 else
 5423182657263) else
 (if i.val < 597 then
 5043569655979 else
 3494616980892))) else
 (if i.val < 602 then
 (if i.val < 600 then
 (if i.val < 599 then
 3081466005019 else
 6008702240005) else
 (if i.val < 601 then
 1836387834727 else
 3632043873548)) else
 (if i.val < 604 then
 (if i.val < 603 then
 4248280641656 else
 4150636892371) else
 (if i.val < 605 then
 655364032297 else
 (if i.val < 606 then
 734013435373 else
 4263110946756))))))) else
 (if i.val < 641 then
 (if i.val < 624 then
 (if i.val < 615 then
 (if i.val < 611 then
 (if i.val < 609 then
 (if i.val < 608 then
 109434662056 else
 4726308518203) else
 (if i.val < 610 then
 7519943222980 else
 7204691828212)) else
 (if i.val < 613 then
 (if i.val < 612 then
 5899729384619 else
 438944220445) else
 (if i.val < 614 then
 4154550561140 else
 6642078446248))) else
 (if i.val < 619 then
 (if i.val < 617 then
 (if i.val < 616 then
 4264469333085 else
 4022995676448) else
 (if i.val < 618 then
 1693311520580 else
 4578855867641)) else
 (if i.val < 621 then
 (if i.val < 620 then
 4200500850177 else
 3880884008647) else
 (if i.val < 622 then
 1530114709803 else
 (if i.val < 623 then
 1075368614367 else
 6660645811267))))) else
 (if i.val < 632 then
 (if i.val < 628 then
 (if i.val < 626 then
 (if i.val < 625 then
 7065064685573 else
 7631006890679) else
 (if i.val < 627 then
 3086312890999 else
 1831649243092)) else
 (if i.val < 630 then
 (if i.val < 629 then
 1394155671963 else
 6809641317344) else
 (if i.val < 631 then
 6077132354545 else
 2767850))) else
 (if i.val < 636 then
 (if i.val < 634 then
 (if i.val < 633 then
 6657355702364 else
 1277093005185) else
 (if i.val < 635 then
 4900783656064 else
 7365445868120)) else
 (if i.val < 638 then
 (if i.val < 637 then
 3898642153403 else
 5280267233473) else
 (if i.val < 639 then
 6682717996056 else
 (if i.val < 640 then
 6008866165756 else
 5467642137103)))))) else
 (if i.val < 658 then
 (if i.val < 649 then
 (if i.val < 645 then
 (if i.val < 643 then
 (if i.val < 642 then
 5466947222680 else
 6924771658312) else
 (if i.val < 644 then
 2713849240319 else
 800375138545)) else
 (if i.val < 647 then
 (if i.val < 646 then
 4778712043100 else
 1019890324905) else
 (if i.val < 648 then
 4534301477387 else
 7528016118710))) else
 (if i.val < 653 then
 (if i.val < 651 then
 (if i.val < 650 then
 4893248464311 else
 445269242062) else
 (if i.val < 652 then
 56330829467 else
 7381060605697)) else
 (if i.val < 655 then
 (if i.val < 654 then
 3380449524744 else
 6284570304141) else
 (if i.val < 656 then
 1018111008345 else
 (if i.val < 657 then
 4907345750884 else
 3362483943505))))) else
 (if i.val < 666 then
 (if i.val < 662 then
 (if i.val < 660 then
 (if i.val < 659 then
 3222303401397 else
 4562837159387) else
 (if i.val < 661 then
 4872518346933 else
 5094245890536)) else
 (if i.val < 664 then
 (if i.val < 663 then
 5817413718071 else
 204093760184) else
 (if i.val < 665 then
 6000610058956 else
 6791837844977))) else
 (if i.val < 670 then
 (if i.val < 668 then
 (if i.val < 667 then
 6162280358636 else
 5126293037247) else
 (if i.val < 669 then
 4457477376628 else
 2461464404712)) else
 (if i.val < 672 then
 (if i.val < 671 then
 2029273115577 else
 3580721800525) else
 (if i.val < 673 then
 4984330754626 else
 (if i.val < 674 then
 4433289007703 else
 841705980966)))))))) else
 (if i.val < 742 then
 (if i.val < 708 then
 (if i.val < 691 then
 (if i.val < 683 then
 (if i.val < 679 then
 (if i.val < 677 then
 (if i.val < 676 then
 2881675213573 else
 2650660364526) else
 (if i.val < 678 then
 1171891705691 else
 4893240016392)) else
 (if i.val < 681 then
 (if i.val < 680 then
 5347765361729 else
 5204545093310) else
 (if i.val < 682 then
 821829234111 else
 1455921513212))) else
 (if i.val < 687 then
 (if i.val < 685 then
 (if i.val < 684 then
 3362731929477 else
 2533837806341) else
 (if i.val < 686 then
 770466596925 else
 1314344488264)) else
 (if i.val < 689 then
 (if i.val < 688 then
 7243624064236 else
 1598625891691) else
 (if i.val < 690 then
 7454394446844 else
 120611419741)))) else
 (if i.val < 699 then
 (if i.val < 695 then
 (if i.val < 693 then
 (if i.val < 692 then
 908093074387 else
 6985194840879) else
 (if i.val < 694 then
 1965034296963 else
 5191939253852)) else
 (if i.val < 697 then
 (if i.val < 696 then
 5228096617926 else
 1947923296427) else
 (if i.val < 698 then
 2327932442252 else
 2998419165562))) else
 (if i.val < 703 then
 (if i.val < 701 then
 (if i.val < 700 then
 4782171530573 else
 1829078888105) else
 (if i.val < 702 then
 3816442617010 else
 1819100898611)) else
 (if i.val < 705 then
 (if i.val < 704 then
 4863274609584 else
 1950643089650) else
 (if i.val < 706 then
 3654797122066 else
 (if i.val < 707 then
 4626753664219 else
 2342857707647)))))) else
 (if i.val < 725 then
 (if i.val < 716 then
 (if i.val < 712 then
 (if i.val < 710 then
 (if i.val < 709 then
 5332892745863 else
 4821533136419) else
 (if i.val < 711 then
 2746723796187 else
 5241838897079)) else
 (if i.val < 714 then
 (if i.val < 713 then
 7048853684392 else
 4992733268908) else
 (if i.val < 715 then
 1269187116229 else
 2680728626728))) else
 (if i.val < 720 then
 (if i.val < 718 then
 (if i.val < 717 then
 895752752033 else
 3631486928705) else
 (if i.val < 719 then
 3262072064929 else
 1539402686483)) else
 (if i.val < 722 then
 (if i.val < 721 then
 1461728223900 else
 5828808188980) else
 (if i.val < 723 then
 6346130522134 else
 (if i.val < 724 then
 3028885381208 else
 7667769724329))))) else
 (if i.val < 733 then
 (if i.val < 729 then
 (if i.val < 727 then
 (if i.val < 726 then
 847814495940 else
 1834623716199) else
 (if i.val < 728 then
 7573833399403 else
 7260186538708)) else
 (if i.val < 731 then
 (if i.val < 730 then
 6077133025425 else
 6882206498583) else
 (if i.val < 732 then
 1209698393199 else
 4035364515110))) else
 (if i.val < 737 then
 (if i.val < 735 then
 (if i.val < 734 then
 1644218767911 else
 2469897776126) else
 (if i.val < 736 then
 2342609753862 else
 1146734481027)) else
 (if i.val < 739 then
 (if i.val < 738 then
 3158301095727 else
 16362074426) else
 (if i.val < 740 then
 155815044640 else
 (if i.val < 741 then
 4837986738285 else
 962528735183))))))) else
 (if i.val < 776 then
 (if i.val < 759 then
 (if i.val < 750 then
 (if i.val < 746 then
 (if i.val < 744 then
 (if i.val < 743 then
 3046314518047 else
 6780959961371) else
 (if i.val < 745 then
 2435325599808 else
 5937819168797)) else
 (if i.val < 748 then
 (if i.val < 747 then
 456849409979 else
 3585802169300) else
 (if i.val < 749 then
 5550817327905 else
 5524318016020))) else
 (if i.val < 754 then
 (if i.val < 752 then
 (if i.val < 751 then
 475330287092 else
 3019179567163) else
 (if i.val < 753 then
 4963819013733 else
 3421822748264)) else
 (if i.val < 756 then
 (if i.val < 755 then
 6173347043066 else
 2134832540987) else
 (if i.val < 757 then
 3263888301033 else
 (if i.val < 758 then
 1248288880647 else
 6179680509744))))) else
 (if i.val < 767 then
 (if i.val < 763 then
 (if i.val < 761 then
 (if i.val < 760 then
 6449824106799 else
 2217367178934) else
 (if i.val < 762 then
 5308912452841 else
 4337948993719)) else
 (if i.val < 765 then
 (if i.val < 764 then
 700364879497 else
 3202638393628) else
 (if i.val < 766 then
 5906480256599 else
 335583994345))) else
 (if i.val < 771 then
 (if i.val < 769 then
 (if i.val < 768 then
 2899900916091 else
 1141820497156) else
 (if i.val < 770 then
 7590483563619 else
 1494108031312)) else
 (if i.val < 773 then
 (if i.val < 772 then
 251162988579 else
 5664326806599) else
 (if i.val < 774 then
 5965618208471 else
 (if i.val < 775 then
 5492584170192 else
 2192835891863)))))) else
 (if i.val < 793 then
 (if i.val < 784 then
 (if i.val < 780 then
 (if i.val < 778 then
 (if i.val < 777 then
 3102415176244 else
 4899019541464) else
 (if i.val < 779 then
 2266118301361 else
 4060449225266)) else
 (if i.val < 782 then
 (if i.val < 781 then
 3048399887987 else
 3697785139233) else
 (if i.val < 783 then
 2277105706047 else
 1690479341544))) else
 (if i.val < 788 then
 (if i.val < 786 then
 (if i.val < 785 then
 2972887584999 else
 7339591969134) else
 (if i.val < 787 then
 896272916641 else
 3682614337519)) else
 (if i.val < 790 then
 (if i.val < 789 then
 2160916370497 else
 1224112015828) else
 (if i.val < 791 then
 2900788169999 else
 (if i.val < 792 then
 849062835745 else
 2098938887091))))) else
 (if i.val < 801 then
 (if i.val < 797 then
 (if i.val < 795 then
 (if i.val < 794 then
 4570628874556 else
 4963818427419) else
 (if i.val < 796 then
 4968079243912 else
 3603957077967)) else
 (if i.val < 799 then
 (if i.val < 798 then
 1550918723348 else
 357646509167) else
 (if i.val < 800 then
 6793177552467 else
 196759427991))) else
 (if i.val < 805 then
 (if i.val < 803 then
 (if i.val < 802 then
 1991483469633 else
 3007401713952) else
 (if i.val < 804 then
 2676196905852 else
 2965196957364)) else
 (if i.val < 807 then
 (if i.val < 806 then
 7104884218387 else
 506141242877) else
 (if i.val < 808 then
 2073289931150 else
 (if i.val < 809 then
 6534439278750 else
 4981208853600))))))))) else
 (if i.val < 945 then
 (if i.val < 877 then
 (if i.val < 843 then
 (if i.val < 826 then
 (if i.val < 818 then
 (if i.val < 814 then
 (if i.val < 812 then
 (if i.val < 811 then
 3490044818680 else
 97292815834) else
 (if i.val < 813 then
 2271460516508 else
 77471102829)) else
 (if i.val < 816 then
 (if i.val < 815 then
 6176401916040 else
 4280324281899) else
 (if i.val < 817 then
 5296579398703 else
 4710367322008))) else
 (if i.val < 822 then
 (if i.val < 820 then
 (if i.val < 819 then
 2554332736725 else
 470614088283) else
 (if i.val < 821 then
 6266878184499 else
 6286848682250)) else
 (if i.val < 824 then
 (if i.val < 823 then
 6684154503466 else
 2650673148019) else
 (if i.val < 825 then
 6176402529047 else
 2961138764173)))) else
 (if i.val < 834 then
 (if i.val < 830 then
 (if i.val < 828 then
 (if i.val < 827 then
 479479255926 else
 4003091230691) else
 (if i.val < 829 then
 3362050405392 else
 4858433261129)) else
 (if i.val < 832 then
 (if i.val < 831 then
 7542825360710 else
 6740166855111) else
 (if i.val < 833 then
 4929229335812 else
 2037528126477))) else
 (if i.val < 838 then
 (if i.val < 836 then
 (if i.val < 835 then
 5508619269805 else
 4344895770897) else
 (if i.val < 837 then
 26775576887 else
 1863161266833)) else
 (if i.val < 840 then
 (if i.val < 839 then
 5698377088836 else
 5414800279571) else
 (if i.val < 841 then
 1452823822484 else
 (if i.val < 842 then
 7516272834140 else
 974416741648)))))) else
 (if i.val < 860 then
 (if i.val < 851 then
 (if i.val < 847 then
 (if i.val < 845 then
 (if i.val < 844 then
 661405526085 else
 4942055338248) else
 (if i.val < 846 then
 4366476251180 else
 415318457441)) else
 (if i.val < 849 then
 (if i.val < 848 then
 6986879907177 else
 1921451897647) else
 (if i.val < 850 then
 200582403603 else
 3587586992967))) else
 (if i.val < 855 then
 (if i.val < 853 then
 (if i.val < 852 then
 6785220839467 else
 1387754606573) else
 (if i.val < 854 then
 2854024469480 else
 6340291858966)) else
 (if i.val < 857 then
 (if i.val < 856 then
 2155178070247 else
 5237807987100) else
 (if i.val < 858 then
 6439805651310 else
 (if i.val < 859 then
 6287135987311 else
 5815745796036))))) else
 (if i.val < 868 then
 (if i.val < 864 then
 (if i.val < 862 then
 (if i.val < 861 then
 1484483902050 else
 1121123692128) else
 (if i.val < 863 then
 1284586012685 else
 1595986041840)) else
 (if i.val < 866 then
 (if i.val < 865 then
 4171976208641 else
 4261355972625) else
 (if i.val < 867 then
 7181568664263 else
 1901755989379))) else
 (if i.val < 872 then
 (if i.val < 870 then
 (if i.val < 869 then
 2641823138292 else
 1487465570419) else
 (if i.val < 871 then
 1861891203805 else
 1578509745727)) else
 (if i.val < 874 then
 (if i.val < 873 then
 412264229348 else
 4968494184656) else
 (if i.val < 875 then
 223030777771 else
 (if i.val < 876 then
 5761086400897 else
 3366501761963))))))) else
 (if i.val < 911 then
 (if i.val < 894 then
 (if i.val < 885 then
 (if i.val < 881 then
 (if i.val < 879 then
 (if i.val < 878 then
 2375302299719 else
 2669478229887) else
 (if i.val < 880 then
 7024372684379 else
 4009136236492)) else
 (if i.val < 883 then
 (if i.val < 882 then
 3555121949008 else
 2871697949929) else
 (if i.val < 884 then
 2150476974028 else
 231646158533))) else
 (if i.val < 889 then
 (if i.val < 887 then
 (if i.val < 886 then
 4758188296805 else
 5328295154629) else
 (if i.val < 888 then
 2307689292983 else
 4775582952380)) else
 (if i.val < 891 then
 (if i.val < 890 then
 4124575628266 else
 910589804347) else
 (if i.val < 892 then
 6161277126000 else
 (if i.val < 893 then
 2826510323010 else
 4136230124611))))) else
 (if i.val < 902 then
 (if i.val < 898 then
 (if i.val < 896 then
 (if i.val < 895 then
 873588141336 else
 4060448080950) else
 (if i.val < 897 then
 3748296891828 else
 5640291522785)) else
 (if i.val < 900 then
 (if i.val < 899 then
 6490105075140 else
 6883011581141) else
 (if i.val < 901 then
 3592038951525 else
 74168948979))) else
 (if i.val < 906 then
 (if i.val < 904 then
 (if i.val < 903 then
 3741108242199 else
 3633550005671) else
 (if i.val < 905 then
 1160856050592 else
 5773311842663)) else
 (if i.val < 908 then
 (if i.val < 907 then
 1858448096644 else
 861293773864) else
 (if i.val < 909 then
 7339592645761 else
 (if i.val < 910 then
 3570148827040 else
 4280333413748)))))) else
 (if i.val < 928 then
 (if i.val < 919 then
 (if i.val < 915 then
 (if i.val < 913 then
 (if i.val < 912 then
 2600008502326 else
 5256812045280) else
 (if i.val < 914 then
 1425815914652 else
 7668589335871)) else
 (if i.val < 917 then
 (if i.val < 916 then
 7588891816348 else
 6631091224761) else
 (if i.val < 918 then
 3062929682566 else
 3098795532210))) else
 (if i.val < 923 then
 (if i.val < 921 then
 (if i.val < 920 then
 7329754975411 else
 2964174310900) else
 (if i.val < 922 then
 4858426660173 else
 2037529387010)) else
 (if i.val < 925 then
 (if i.val < 924 then
 789390926211 else
 1250910782426) else
 (if i.val < 926 then
 2186699678562 else
 (if i.val < 927 then
 755249362527 else
 3591638588427))))) else
 (if i.val < 936 then
 (if i.val < 932 then
 (if i.val < 930 then
 (if i.val < 929 then
 2048439378326 else
 5715085343740) else
 (if i.val < 931 then
 1971607402185 else
 7391969549483)) else
 (if i.val < 934 then
 (if i.val < 933 then
 1976973188347 else
 3470358654083) else
 (if i.val < 935 then
 4748780055784 else
 5626984129445))) else
 (if i.val < 940 then
 (if i.val < 938 then
 (if i.val < 937 then
 6569976194320 else
 1419443148962) else
 (if i.val < 939 then
 6106352240333 else
 5019155898325)) else
 (if i.val < 942 then
 (if i.val < 941 then
 5787865166229 else
 4379521233897) else
 (if i.val < 943 then
 3484627704534 else
 (if i.val < 944 then
 3280619592961 else
 2196631109873)))))))) else
 (if i.val < 1012 then
 (if i.val < 978 then
 (if i.val < 961 then
 (if i.val < 953 then
 (if i.val < 949 then
 (if i.val < 947 then
 (if i.val < 946 then
 321881141900 else
 2268570860608) else
 (if i.val < 948 then
 1208632249828 else
 6416447113956)) else
 (if i.val < 951 then
 (if i.val < 950 then
 5722832838862 else
 6280892080903) else
 (if i.val < 952 then
 6882204199767 else
 7391978629148))) else
 (if i.val < 957 then
 (if i.val < 955 then
 (if i.val < 954 then
 1019877800567 else
 1411276539867) else
 (if i.val < 956 then
 5932040418591 else
 1833498911433)) else
 (if i.val < 959 then
 (if i.val < 958 then
 1193782598952 else
 6647190414852) else
 (if i.val < 960 then
 1819627221564 else
 4174706930587)))) else
 (if i.val < 969 then
 (if i.val < 965 then
 (if i.val < 963 then
 (if i.val < 962 then
 6412867308677 else
 2045639772950) else
 (if i.val < 964 then
 2080897798950 else
 255214650671)) else
 (if i.val < 967 then
 (if i.val < 966 then
 1812758509908 else
 2840507246897) else
 (if i.val < 968 then
 579885203279 else
 138926129000))) else
 (if i.val < 973 then
 (if i.val < 971 then
 (if i.val < 970 then
 4376412574005 else
 2455004100520) else
 (if i.val < 972 then
 5803305120392 else
 2669916154063)) else
 (if i.val < 975 then
 (if i.val < 974 then
 1659070368633 else
 1019877207164) else
 (if i.val < 976 then
 7455492922834 else
 (if i.val < 977 then
 2145079182361 else
 7122429563683)))))) else
 (if i.val < 995 then
 (if i.val < 986 then
 (if i.val < 982 then
 (if i.val < 980 then
 (if i.val < 979 then
 1355973641180 else
 7306045030891) else
 (if i.val < 981 then
 2711574781425 else
 5647133668385)) else
 (if i.val < 984 then
 (if i.val < 983 then
 416414423645 else
 1455929543884) else
 (if i.val < 985 then
 4261841083534 else
 5353205708729))) else
 (if i.val < 990 then
 (if i.val < 988 then
 (if i.val < 987 then
 5122529545840 else
 6791840445352) else
 (if i.val < 989 then
 1420485847120 else
 3415561380179)) else
 (if i.val < 992 then
 (if i.val < 991 then
 565419002899 else
 6938042378992) else
 (if i.val < 993 then
 2976320542263 else
 (if i.val < 994 then
 7030263493244 else
 1425806879245))))) else
 (if i.val < 1003 then
 (if i.val < 999 then
 (if i.val < 997 then
 (if i.val < 996 then
 5610672095750 else
 1754510236664) else
 (if i.val < 998 then
 1394737094685 else
 5245384388764)) else
 (if i.val < 1001 then
 (if i.val < 1000 then
 6221371317620 else
 7167269446103) else
 (if i.val < 1002 then
 488477562385 else
 3928045924483))) else
 (if i.val < 1007 then
 (if i.val < 1005 then
 (if i.val < 1004 then
 6416447746050 else
 974407753484) else
 (if i.val < 1006 then
 4630760627528 else
 5174486714262)) else
 (if i.val < 1009 then
 (if i.val < 1008 then
 2728255179134 else
 2396757041936) else
 (if i.val < 1010 then
 4685542809061 else
 (if i.val < 1011 then
 5389961836466 else
 6300249342256))))))) else
 (if i.val < 1046 then
 (if i.val < 1029 then
 (if i.val < 1020 then
 (if i.val < 1016 then
 (if i.val < 1014 then
 (if i.val < 1013 then
 5432149662677 else
 5858731433936) else
 (if i.val < 1015 then
 7175447562147 else
 884063341528)) else
 (if i.val < 1018 then
 (if i.val < 1017 then
 3421281595212 else
 2881688107677) else
 (if i.val < 1019 then
 316050303025 else
 4323293621926))) else
 (if i.val < 1024 then
 (if i.val < 1022 then
 (if i.val < 1021 then
 6755876031803 else
 1663155213066) else
 (if i.val < 1023 then
 1758860579826 else
 4191813731927)) else
 (if i.val < 1026 then
 (if i.val < 1025 then
 2766080589752 else
 4203918804262) else
 (if i.val < 1027 then
 470429738873 else
 (if i.val < 1028 then
 1806705099605 else
 7429189593310))))) else
 (if i.val < 1037 then
 (if i.val < 1033 then
 (if i.val < 1031 then
 (if i.val < 1030 then
 1578509222111 else
 5155612734684) else
 (if i.val < 1032 then
 5641383863471 else
 4987913793544)) else
 (if i.val < 1035 then
 (if i.val < 1034 then
 3866864981061 else
 5325321432620) else
 (if i.val < 1036 then
 534135145208 else
 895752323277))) else
 (if i.val < 1041 then
 (if i.val < 1039 then
 (if i.val < 1038 then
 4513789907636 else
 2037528842791) else
 (if i.val < 1040 then
 7128754596527 else
 3403537985827)) else
 (if i.val < 1043 then
 (if i.val < 1042 then
 5312501490320 else
 3789376194512) else
 (if i.val < 1044 then
 250972626612 else
 (if i.val < 1045 then
 2932023812300 else
 421352046105)))))) else
 (if i.val < 1063 then
 (if i.val < 1054 then
 (if i.val < 1050 then
 (if i.val < 1048 then
 (if i.val < 1047 then
 1243394392187 else
 7519944079910) else
 (if i.val < 1049 then
 962520435111 else
 5404493993662)) else
 (if i.val < 1052 then
 (if i.val < 1051 then
 6702722595467 else
 7502224650097) else
 (if i.val < 1053 then
 2230264093944 else
 5044254553341))) else
 (if i.val < 1058 then
 (if i.val < 1056 then
 (if i.val < 1055 then
 6165995862345 else
 3802211267284) else
 (if i.val < 1057 then
 6632984925671 else
 829117284544)) else
 (if i.val < 1060 then
 (if i.val < 1059 then
 940823240061 else
 4102438222820) else
 (if i.val < 1061 then
 3132325717808 else
 (if i.val < 1062 then
 151080844677 else
 5228841936236))))) else
 (if i.val < 1071 then
 (if i.val < 1067 then
 (if i.val < 1065 then
 (if i.val < 1064 then
 1829400845791 else
 6759199431527) else
 (if i.val < 1066 then
 858744020827 else
 2676209752520)) else
 (if i.val < 1069 then
 (if i.val < 1068 then
 7617201976712 else
 245892319212) else
 (if i.val < 1070 then
 7404037799741 else
 1390537406325))) else
 (if i.val < 1075 then
 (if i.val < 1073 then
 (if i.val < 1072 then
 3135257793664 else
 4662195750436) else
 (if i.val < 1074 then
 751497261091 else
 2285495048244)) else
 (if i.val < 1077 then
 (if i.val < 1076 then
 3106815262741 else
 2865800648587) else
 (if i.val < 1078 then
 4847454459879 else
 (if i.val < 1079 then
 2892837627963 else
 5325308754452)))))))))))

def orbitCode (i : Fin 560) : Nat :=
 (if i.val < 280 then
 (if i.val < 140 then
 (if i.val < 70 then
 (if i.val < 35 then
 (if i.val < 17 then
 (if i.val < 8 then
 (if i.val < 4 then
 (if i.val < 2 then
 (if i.val < 1 then
 252721728214 else
 35068724103) else
 (if i.val < 3 then
 58040238342 else
 88611669638)) else
 (if i.val < 6 then
 (if i.val < 5 then
 252394534824 else
 222761150133) else
 (if i.val < 7 then
 258227832506 else
 285474678037))) else
 (if i.val < 12 then
 (if i.val < 10 then
 (if i.val < 9 then
 148087100634 else
 203813372711) else
 (if i.val < 11 then
 114012668738 else
 130669468300)) else
 (if i.val < 14 then
 (if i.val < 13 then
 353214829 else
 67562220609) else
 (if i.val < 15 then
 116652023117 else
 (if i.val < 16 then
 188554881120 else
 355901831701))))) else
 (if i.val < 26 then
 (if i.val < 21 then
 (if i.val < 19 then
 (if i.val < 18 then
 197435161915 else
 355208129734) else
 (if i.val < 20 then
 324233903952 else
 352436938218)) else
 (if i.val < 23 then
 (if i.val < 22 then
 63504625311 else
 324307086203) else
 (if i.val < 24 then
 295417000200 else
 (if i.val < 25 then
 8071077117 else
 252421769525)))) else
 (if i.val < 30 then
 (if i.val < 28 then
 (if i.val < 27 then
 91809874808 else
 360645894251) else
 (if i.val < 29 then
 264227473730 else
 84789362013)) else
 (if i.val < 32 then
 (if i.val < 31 then
 180317522807 else
 278067720024) else
 (if i.val < 33 then
 301604118312 else
 (if i.val < 34 then
 324233315918 else
 28985681738)))))) else
 (if i.val < 52 then
 (if i.val < 43 then
 (if i.val < 39 then
 (if i.val < 37 then
 (if i.val < 36 then
 324960894602 else
 148064152807) else
 (if i.val < 38 then
 646148 else
 79961256209)) else
 (if i.val < 41 then
 (if i.val < 40 then
 137685183300 else
 21394846143) else
 (if i.val < 42 then
 1653572425 else
 201930674439))) else
 (if i.val < 47 then
 (if i.val < 45 then
 (if i.val < 44 then
 108073576843 else
 67206636305) else
 (if i.val < 46 then
 248525676742 else
 127349158904)) else
 (if i.val < 49 then
 (if i.val < 48 then
 289439792708 else
 172707344811) else
 (if i.val < 50 then
 70313495628 else
 (if i.val < 51 then
 21395461500 else
 256344536701))))) else
 (if i.val < 61 then
 (if i.val < 56 then
 (if i.val < 54 then
 (if i.val < 53 then
 230180284113 else
 49386211348) else
 (if i.val < 55 then
 27203961828 else
 227343169051)) else
 (if i.val < 58 then
 (if i.val < 57 then
 161501619329 else
 150272298934) else
 (if i.val < 59 then
 292432355709 else
 (if i.val < 60 then
 93724711352 else
 182041239810)))) else
 (if i.val < 65 then
 (if i.val < 63 then
 (if i.val < 62 then
 142030093210 else
 191064253418) else
 (if i.val < 64 then
 116878278802 else
 100093267306)) else
 (if i.val < 67 then
 (if i.val < 66 then
 286251919005 else
 277004527148) else
 (if i.val < 68 then
 267993011248 else
 (if i.val < 69 then
 215070592739 else
 4793124506))))))) else
 (if i.val < 105 then
 (if i.val < 87 then
 (if i.val < 78 then
 (if i.val < 74 then
 (if i.val < 72 then
 (if i.val < 71 then
 9020072042 else
 137684620433) else
 (if i.val < 73 then
 174555647820 else
 3717792505)) else
 (if i.val < 76 then
 (if i.val < 75 then
 204574294629 else
 342196535516) else
 (if i.val < 77 then
 98162759639 else
 317262450000))) else
 (if i.val < 82 then
 (if i.val < 80 then
 (if i.val < 79 then
 44204322710 else
 9685968143) else
 (if i.val < 81 then
 263331830733 else
 6658944407)) else
 (if i.val < 84 then
 (if i.val < 83 then
 224255705538 else
 362992594707) else
 (if i.val < 85 then
 354488502439 else
 (if i.val < 86 then
 69623472003 else
 318459968200))))) else
 (if i.val < 96 then
 (if i.val < 91 then
 (if i.val < 89 then
 (if i.val < 88 then
 223272915511 else
 123558934918) else
 (if i.val < 90 then
 58522976906 else
 145730300717)) else
 (if i.val < 93 then
 (if i.val < 92 then
 289687217009 else
 291603829639) else
 (if i.val < 94 then
 338491556402 else
 (if i.val < 95 then
 50532971225 else
 253896368538)))) else
 (if i.val < 100 then
 (if i.val < 98 then
 (if i.val < 97 then
 227499874007 else
 236545870412) else
 (if i.val < 99 then
 7902442101 else
 33248401500)) else
 (if i.val < 102 then
 (if i.val < 101 then
 306781903938 else
 285497782342) else
 (if i.val < 103 then
 10957895825 else
 (if i.val < 104 then
 176387025713 else
 108268403114)))))) else
 (if i.val < 122 then
 (if i.val < 113 then
 (if i.val < 109 then
 (if i.val < 107 then
 (if i.val < 106 then
 88605750843 else
 135491057428) else
 (if i.val < 108 then
 365447509621 else
 38654717217)) else
 (if i.val < 111 then
 (if i.val < 110 then
 314543309322 else
 163666878907) else
 (if i.val < 112 then
 14860677813 else
 6675314800))) else
 (if i.val < 117 then
 (if i.val < 115 then
 (if i.val < 114 then
 81317315518 else
 116624934811) else
 (if i.val < 116 then
 80486926520 else
 103734232312)) else
 (if i.val < 119 then
 (if i.val < 118 then
 211802920339 else
 269555878014) else
 (if i.val < 120 then
 347232160411 else
 (if i.val < 121 then
 170386221802 else
 311186081843))))) else
 (if i.val < 131 then
 (if i.val < 126 then
 (if i.val < 124 then
 (if i.val < 123 then
 141700558930 else
 225490156813) else
 (if i.val < 125 then
 19029583128 else
 1971239)) else
 (if i.val < 128 then
 (if i.val < 127 then
 113015506903 else
 62491724930) else
 (if i.val < 129 then
 59510666505 else
 (if i.val < 130 then
 304553250317 else
 178235327452)))) else
 (if i.val < 135 then
 (if i.val < 133 then
 (if i.val < 132 then
 113807799000 else
 353929125311) else
 (if i.val < 134 then
 1374942 else
 329582296552)) else
 (if i.val < 137 then
 (if i.val < 136 then
 207442331917 else
 280901945300) else
 (if i.val < 138 then
 135959207216 else
 (if i.val < 139 then
 156747396100 else
 29212615924)))))))) else
 (if i.val < 210 then
 (if i.val < 175 then
 (if i.val < 157 then
 (if i.val < 148 then
 (if i.val < 144 then
 (if i.val < 142 then
 (if i.val < 141 then
 323823397022 else
 37385885528) else
 (if i.val < 143 then
 211651749303 else
 90977216039)) else
 (if i.val < 146 then
 (if i.val < 145 then
 72374175912 else
 248931625813) else
 (if i.val < 147 then
 342881259718 else
 353213662934))) else
 (if i.val < 152 then
 (if i.val < 150 then
 (if i.val < 149 then
 215134801122 else
 63504183842) else
 (if i.val < 151 then
 291582129934 else
 347575119128)) else
 (if i.val < 154 then
 (if i.val < 153 then
 179314316728 else
 17683937022) else
 (if i.val < 155 then
 17729902329 else
 (if i.val < 156 then
 84708478513 else
 63995895318))))) else
 (if i.val < 166 then
 (if i.val < 161 then
 (if i.val < 159 then
 (if i.val < 158 then
 260414373216 else
 335283775028) else
 (if i.val < 160 then
 123630389309 else
 311470383529)) else
 (if i.val < 163 then
 (if i.val < 162 then
 116717526210 else
 218444284404) else
 (if i.val < 164 then
 278042486408 else
 (if i.val < 165 then
 185439744009 else
 178234762624)))) else
 (if i.val < 170 then
 (if i.val < 168 then
 (if i.val < 167 then
 170375389806 else
 18011150033) else
 (if i.val < 169 then
 304737153603 else
 131881081024)) else
 (if i.val < 172 then
 (if i.val < 171 then
 139710821833 else
 17710566311) else
 (if i.val < 173 then
 122238151343 else
 (if i.val < 174 then
 12318775807 else
 340155456125)))))) else
 (if i.val < 192 then
 (if i.val < 183 then
 (if i.val < 179 then
 (if i.val < 177 then
 (if i.val < 176 then
 363974899548 else
 345965770703) else
 (if i.val < 178 then
 99428126622 else
 227676572029)) else
 (if i.val < 181 then
 (if i.val < 180 then
 95339680904 else
 74547262203) else
 (if i.val < 182 then
 28973767905 else
 217145192025))) else
 (if i.val < 187 then
 (if i.val < 185 then
 (if i.val < 184 then
 306760827352 else
 191986722201) else
 (if i.val < 186 then
 362937073201 else
 114034657615)) else
 (if i.val < 189 then
 (if i.val < 188 then
 192890901506 else
 80090863551) else
 (if i.val < 190 then
 264317783703 else
 (if i.val < 191 then
 265299377243 else
 338273943618))))) else
 (if i.val < 201 then
 (if i.val < 196 then
 (if i.val < 194 then
 (if i.val < 193 then
 125753273133 else
 286253284004) else
 (if i.val < 195 then
 195971764207 else
 341273150300)) else
 (if i.val < 198 then
 (if i.val < 197 then
 192699796708 else
 117575774516) else
 (if i.val < 199 then
 290034496900 else
 (if i.val < 200 then
 222462010512 else
 193290088408)))) else
 (if i.val < 205 then
 (if i.val < 203 then
 (if i.val < 202 then
 93490227321 else
 331000633238) else
 (if i.val < 204 then
 125562169720 else
 97286560237)) else
 (if i.val < 207 then
 (if i.val < 206 then
 213430537901 else
 2354733614) else
 (if i.val < 208 then
 130386660109 else
 (if i.val < 209 then
 117377412200 else
 143492677905))))))) else
 (if i.val < 245 then
 (if i.val < 227 then
 (if i.val < 218 then
 (if i.val < 214 then
 (if i.val < 212 then
 (if i.val < 211 then
 257839794812 else
 184647504404) else
 (if i.val < 213 then
 150870029400 else
 176707692522)) else
 (if i.val < 216 then
 (if i.val < 215 then
 148505264307 else
 95362093215) else
 (if i.val < 217 then
 29212093608 else
 254629))) else
 (if i.val < 222 then
 (if i.val < 220 then
 (if i.val < 219 then
 310190080803 else
 215082865215) else
 (if i.val < 221 then
 309363327804 else
 225828352008)) else
 (if i.val < 224 then
 (if i.val < 223 then
 192358720639 else
 338468724300) else
 (if i.val < 225 then
 80816668025 else
 (if i.val < 226 then
 222099157805 else
 291694098903))))) else
 (if i.val < 236 then
 (if i.val < 231 then
 (if i.val < 229 then
 (if i.val < 228 then
 174299396016 else
 75705506100) else
 (if i.val < 230 then
 17753571100 else
 335277804929)) else
 (if i.val < 233 then
 (if i.val < 232 then
 206348961821 else
 101875205624) else
 (if i.val < 234 then
 269761639711 else
 (if i.val < 235 then
 257145514100 else
 144909149604)))) else
 (if i.val < 240 then
 (if i.val < 238 then
 (if i.val < 237 then
 131414248316 else
 79137755912) else
 (if i.val < 239 then
 113952463921 else
 219428979438)) else
 (if i.val < 242 then
 (if i.val < 241 then
 9750867902 else
 123473831114) else
 (if i.val < 243 then
 280878474712 else
 (if i.val < 244 then
 131706369209 else
 81201942110)))))) else
 (if i.val < 262 then
 (if i.val < 253 then
 (if i.val < 249 then
 (if i.val < 247 then
 (if i.val < 246 then
 231857018015 else
 22230919007) else
 (if i.val < 248 then
 275380845533 else
 324053941804)) else
 (if i.val < 251 then
 (if i.val < 250 then
 137516083200 else
 163145693315) else
 (if i.val < 252 then
 24282404351 else
 131681581916))) else
 (if i.val < 257 then
 (if i.val < 255 then
 (if i.val < 254 then
 303127867139 else
 203008670413) else
 (if i.val < 256 then
 201797256425 else
 75971037018)) else
 (if i.val < 259 then
 (if i.val < 258 then
 355600921934 else
 39556029533) else
 (if i.val < 260 then
 145615573704 else
 (if i.val < 261 then
 183306105108 else
 61797552402))))) else
 (if i.val < 271 then
 (if i.val < 266 then
 (if i.val < 264 then
 (if i.val < 263 then
 135959945652 else
 329583041030) else
 (if i.val < 265 then
 207187854300 else
 338711895901)) else
 (if i.val < 268 then
 (if i.val < 267 then
 269676396228 else
 17711274338) else
 (if i.val < 269 then
 343144478724 else
 (if i.val < 270 then
 1105282717 else
 252359766318)))) else
 (if i.val < 275 then
 (if i.val < 273 then
 (if i.val < 272 then
 201914608433 else
 302082794302) else
 (if i.val < 274 then
 365145291043 else
 24260658542)) else
 (if i.val < 277 then
 (if i.val < 276 then
 172950134110 else
 192335789503) else
 (if i.val < 278 then
 215156103522 else
 (if i.val < 279 then
 143163737302 else
 277021100300))))))))) else
 (if i.val < 420 then
 (if i.val < 350 then
 (if i.val < 315 then
 (if i.val < 297 then
 (if i.val < 288 then
 (if i.val < 284 then
 (if i.val < 282 then
 (if i.val < 281 then
 64513129252 else
 307356054101) else
 (if i.val < 283 then
 314056028800 else
 350013810422)) else
 (if i.val < 286 then
 (if i.val < 285 then
 325149273429 else
 236567242003) else
 (if i.val < 287 then
 140692531702 else
 173288833239))) else
 (if i.val < 292 then
 (if i.val < 290 then
 (if i.val < 289 then
 281709515321 else
 365144700216) else
 (if i.val < 291 then
 60295261430 else
 24575773720)) else
 (if i.val < 294 then
 (if i.val < 293 then
 295012700417 else
 11173407700) else
 (if i.val < 295 then
 67768778312 else
 (if i.val < 296 then
 294050464738 else
 242152576934))))) else
 (if i.val < 306 then
 (if i.val < 301 then
 (if i.val < 299 then
 (if i.val < 298 then
 309385170933 else
 284051308916) else
 (if i.val < 300 then
 35511170717 else
 148216255805)) else
 (if i.val < 303 then
 (if i.val < 302 then
 6434204513 else
 8797158614) else
 (if i.val < 304 then
 12251776409 else
 (if i.val < 305 then
 88638016707 else
 282858651321)))) else
 (if i.val < 310 then
 (if i.val < 308 then
 (if i.val < 307 then
 258895267443 else
 271636589537) else
 (if i.val < 309 then
 264200573915 else
 85051556438)) else
 (if i.val < 312 then
 (if i.val < 311 then
 71407269422 else
 199733128800) else
 (if i.val < 313 then
 168739548628 else
 (if i.val < 314 then
 200790320321 else
 8070800611)))))) else
 (if i.val < 332 then
 (if i.val < 323 then
 (if i.val < 319 then
 (if i.val < 317 then
 (if i.val < 316 then
 257465526034 else
 253897208739) else
 (if i.val < 318 then
 315914610401 else
 222124041016)) else
 (if i.val < 321 then
 (if i.val < 320 then
 145707561830 else
 230620877442) else
 (if i.val < 322 then
 329561923852 else
 284359779910))) else
 (if i.val < 327 then
 (if i.val < 325 then
 (if i.val < 324 then
 102377880706 else
 268013853848) else
 (if i.val < 326 then
 131613313421 else
 179005442000)) else
 (if i.val < 329 then
 (if i.val < 328 then
 113076194143 else
 222486934624) else
 (if i.val < 330 then
 177035611728 else
 (if i.val < 331 then
 218642830121 else
 4074911100))))) else
 (if i.val < 341 then
 (if i.val < 336 then
 (if i.val < 334 then
 (if i.val < 333 then
 72657417228 else
 1130141816) else
 (if i.val < 335 then
 266143221214 else
 33566778234)) else
 (if i.val < 338 then
 (if i.val < 337 then
 342327460330 else
 183341872109) else
 (if i.val < 339 then
 146156953802 else
 (if i.val < 340 then
 218279958930 else
 267714496605)))) else
 (if i.val < 345 then
 (if i.val < 343 then
 (if i.val < 342 then
 121724848825 else
 302731207233) else
 (if i.val < 344 then
 8316986717 else
 59841715237)) else
 (if i.val < 347 then
 (if i.val < 346 then
 63132433225 else
 131485115920) else
 (if i.val < 348 then
 274312870106 else
 (if i.val < 349 then
 9046382648 else
 100424405134))))))) else
 (if i.val < 385 then
 (if i.val < 367 then
 (if i.val < 358 then
 (if i.val < 354 then
 (if i.val < 352 then
 (if i.val < 351 then
 214654192704 else
 324053442328) else
 (if i.val < 353 then
 136932556406 else
 201891709225)) else
 (if i.val < 356 then
 (if i.val < 355 then
 69873547300 else
 117585012307) else
 (if i.val < 357 then
 237723694518 else
 226748994848))) else
 (if i.val < 362 then
 (if i.val < 360 then
 (if i.val < 359 then
 275690622300 else
 121951067108) else
 (if i.val < 361 then
 139710415430 else
 210563341005)) else
 (if i.val < 364 then
 (if i.val < 363 then
 143184992502 else
 88615099152) else
 (if i.val < 365 then
 122076264017 else
 (if i.val < 366 then
 197414387615 else
 225224302020))))) else
 (if i.val < 376 then
 (if i.val < 371 then
 (if i.val < 369 then
 (if i.val < 368 then
 157967518330 else
 19286878701) else
 (if i.val < 370 then
 316082198815 else
 197984114000)) else
 (if i.val < 373 then
 (if i.val < 372 then
 91568949822 else
 271350588243) else
 (if i.val < 374 then
 173105667616 else
 (if i.val < 375 then
 139825942905 else
 125716564502)))) else
 (if i.val < 380 then
 (if i.val < 378 then
 (if i.val < 377 then
 319198133200 else
 131607318014) else
 (if i.val < 379 then
 322555379551 else
 50845959609)) else
 (if i.val < 382 then
 (if i.val < 381 then
 12294193824 else
 318980411805) else
 (if i.val < 383 then
 143469871106 else
 (if i.val < 384 then
 148651192730 else
 248448638117)))))) else
 (if i.val < 402 then
 (if i.val < 393 then
 (if i.val < 389 then
 (if i.val < 387 then
 (if i.val < 386 then
 309475377425 else
 89270117308) else
 (if i.val < 388 then
 265588670910 else
 59014394800)) else
 (if i.val < 391 then
 (if i.val < 390 then
 188167016604 else
 79486877520) else
 (if i.val < 392 then
 338738634111 else
 123451002421))) else
 (if i.val < 397 then
 (if i.val < 395 then
 (if i.val < 394 then
 199792491537 else
 63157286321) else
 (if i.val < 396 then
 12228894652 else
 39645688401)) else
 (if i.val < 399 then
 (if i.val < 398 then
 311211170124 else
 123653619304) else
 (if i.val < 400 then
 211959863517 else
 (if i.val < 401 then
 190127793715 else
 167739912251))))) else
 (if i.val < 411 then
 (if i.val < 406 then
 (if i.val < 404 then
 (if i.val < 403 then
 312170386500 else
 13417935820) else
 (if i.val < 405 then
 135479281251 else
 310308817300)) else
 (if i.val < 408 then
 (if i.val < 407 then
 360477582337 else
 170717954001) else
 (if i.val < 409 then
 238760374434 else
 (if i.val < 410 then
 302356304209 else
 93700304430)))) else
 (if i.val < 415 then
 (if i.val < 413 then
 (if i.val < 412 then
 173096635037 else
 114152828552) else
 (if i.val < 414 then
 265667326408 else
 278533842310)) else
 (if i.val < 417 then
 (if i.val < 416 then
 115649713624 else
 306727202200) else
 (if i.val < 418 then
 333325702222 else
 (if i.val < 419 then
 144797447914 else
 287876798737)))))))) else
 (if i.val < 490 then
 (if i.val < 455 then
 (if i.val < 437 then
 (if i.val < 428 then
 (if i.val < 424 then
 (if i.val < 422 then
 (if i.val < 421 then
 218807429542 else
 139463115220) else
 (if i.val < 423 then
 347257276637 else
 252385930113)) else
 (if i.val < 426 then
 (if i.val < 425 then
 319657834114 else
 235618457004) else
 (if i.val < 427 then
 145859485310 else
 338297773900))) else
 (if i.val < 432 then
 (if i.val < 430 then
 (if i.val < 429 then
 121912430000 else
 33567479824) else
 (if i.val < 431 then
 22910299307 else
 340143625015)) else
 (if i.val < 434 then
 (if i.val < 433 then
 294508441222 else
 213116273000) else
 (if i.val < 435 then
 101876014114 else
 (if i.val < 436 then
 110578481608 else
 183858469233))))) else
 (if i.val < 446 then
 (if i.val < 441 then
 (if i.val < 439 then
 (if i.val < 438 then
 307965850421 else
 263331007148) else
 (if i.val < 440 then
 64807221600 else
 45943511151)) else
 (if i.val < 443 then
 (if i.val < 442 then
 241652557948 else
 47038203100) else
 (if i.val < 444 then
 343493625342 else
 (if i.val < 445 then
 113974444622 else
 4098009918)))) else
 (if i.val < 450 then
 (if i.val < 448 then
 (if i.val < 447 then
 299723646600 else
 349631745243) else
 (if i.val < 449 then
 82164994200 else
 93135462512)) else
 (if i.val < 452 then
 (if i.val < 451 then
 307966470551 else
 259496590237) else
 (if i.val < 453 then
 325170613606 else
 (if i.val < 454 then
 298808593224 else
 67886276601)))))) else
 (if i.val < 472 then
 (if i.val < 463 then
 (if i.val < 459 then
 (if i.val < 457 then
 (if i.val < 456 then
 59775304206 else
 5500555720) else
 (if i.val < 458 then
 122509397322 else
 97773683210)) else
 (if i.val < 461 then
 (if i.val < 460 then
 244946320851 else
 62479975429) else
 (if i.val < 462 then
 198117867416 else
 364856389315))) else
 (if i.val < 467 then
 (if i.val < 465 then
 (if i.val < 464 then
 131616480852 else
 37772689100) else
 (if i.val < 466 then
 115640690509 else
 350001900651)) else
 (if i.val < 469 then
 (if i.val < 468 then
 159638078505 else
 112235669000) else
 (if i.val < 470 then
 286252958648 else
 (if i.val < 471 then
 64488524221 else
 244572563413))))) else
 (if i.val < 481 then
 (if i.val < 476 then
 (if i.val < 474 then
 (if i.val < 473 then
 61480855800 else
 38492409348) else
 (if i.val < 475 then
 69859152000 else
 69646868029)) else
 (if i.val < 478 then
 (if i.val < 477 then
 87039104237 else
 168740327011) else
 (if i.val < 479 then
 353930087052 else
 (if i.val < 480 then
 308799306637 else
 98175288605)))) else
 (if i.val < 485 then
 (if i.val < 483 then
 (if i.val < 482 then
 136484530811 else
 265276691238) else
 (if i.val < 484 then
 324955331929 else
 319137761200)) else
 (if i.val < 487 then
 (if i.val < 486 then
 263330446412 else
 103757597621) else
 (if i.val < 488 then
 136963536937 else
 (if i.val < 489 then
 154540235128 else
 54043039609))))))) else
 (if i.val < 525 then
 (if i.val < 507 then
 (if i.val < 498 then
 (if i.val < 494 then
 (if i.val < 492 then
 (if i.val < 491 then
 145905508143 else
 136459741814) else
 (if i.val < 493 then
 302060635842 else
 347132146818)) else
 (if i.val < 496 then
 (if i.val < 495 then
 24804595942 else
 146611921016) else
 (if i.val < 497 then
 144893080530 else
 264227380024))) else
 (if i.val < 502 then
 (if i.val < 500 then
 (if i.val < 499 then
 278043432142 else
 286254197751) else
 (if i.val < 501 then
 107456569400 else
 134090752937)) else
 (if i.val < 504 then
 (if i.val < 503 then
 210255636548 else
 355232245600) else
 (if i.val < 505 then
 2669529130 else
 (if i.val < 506 then
 188862048520 else
 292423768311))))) else
 (if i.val < 516 then
 (if i.val < 511 then
 (if i.val < 509 then
 (if i.val < 508 then
 240663775202 else
 17995167251) else
 (if i.val < 510 then
 359417468300 else
 199220464534)) else
 (if i.val < 513 then
 (if i.val < 512 then
 99442980234 else
 278030744739) else
 (if i.val < 514 then
 280243103542 else
 (if i.val < 515 then
 140327462525 else
 85076563852)))) else
 (if i.val < 520 then
 (if i.val < 518 then
 (if i.val < 517 then
 51097086114 else
 77399235500) else
 (if i.val < 519 then
 207362290710 else
 10902083604)) else
 (if i.val < 522 then
 (if i.val < 521 then
 79474913133 else
 12915466600) else
 (if i.val < 523 then
 178429873329 else
 (if i.val < 524 then
 23068245314 else
 332395019808)))))) else
 (if i.val < 542 then
 (if i.val < 533 then
 (if i.val < 529 then
 (if i.val < 527 then
 (if i.val < 526 then
 223248579929 else
 10981319312) else
 (if i.val < 528 then
 17972203906 else
 12219951717)) else
 (if i.val < 531 then
 (if i.val < 530 then
 257451836613 else
 220118139643) else
 (if i.val < 532 then
 339981640813 else
 314342959300))) else
 (if i.val < 537 then
 (if i.val < 535 then
 (if i.val < 534 then
 248596966018 else
 63145327739) else
 (if i.val < 536 then
 323898801400 else
 112370608712)) else
 (if i.val < 539 then
 (if i.val < 538 then
 316604311138 else
 339567963800) else
 (if i.val < 540 then
 339878226302 else
 (if i.val < 541 then
 6357034607 else
 342196426720))))) else
 (if i.val < 551 then
 (if i.val < 546 then
 (if i.val < 544 then
 (if i.val < 543 then
 48553930734 else
 273891524501) else
 (if i.val < 545 then
 45278334306 else
 160285894551)) else
 (if i.val < 548 then
 (if i.val < 547 then
 41820090200 else
 213384311215) else
 (if i.val < 549 then
 13527549038 else
 (if i.val < 550 then
 360658558312 else
 208169126010)))) else
 (if i.val < 555 then
 (if i.val < 553 then
 (if i.val < 552 then
 19100179108 else
 319001754425) else
 (if i.val < 554 then
 115433937613 else
 244124492448)) else
 (if i.val < 557 then
 (if i.val < 556 then
 100217776615 else
 297645664820) else
 (if i.val < 558 then
 140680711733 else
 (if i.val < 559 then
 235669390603 else
 129415708410))))))))))

def centralIndex (i : Fin 1080) : Index := indexOfCode (centralCode i)
def fusionClass (i : Fin 1080) : Fin 21 :=
  ⟨centralCode i / 604800 % 21, Nat.mod_lt _ (by decide)⟩
def fusionConjugator (i : Fin 1080) : Index := indexOfCode (centralCode i / 12700800)
def orbitIndex (i : Fin 560) : Index := indexOfCode (orbitCode i)
def rightRepresentative (i : Fin 560) : Index := indexOfCode (orbitCode i / 604800)

def centralDecode (x : Index) : Nat :=
  let n := indexCode x
 (if n < 302485 then
 (if n < 150452 then
 (if n < 80273 then
 (if n < 44363 then
 (if n < 25648 then
 (if n < 12973 then
 (if n < 4408 then
 (if n < 2829 then
 (if n < 634 then
 (if n < 280 then
 0 else
 1) else
 (if n < 2108 then
 2 else
 3)) else
 (if n < 4299 then
 (if n < 3240 then
 4 else
 5) else
 (if n < 4303 then
 6 else
 7))) else
 (if n < 7850 then
 (if n < 5883 then
 (if n < 4725 then
 8 else
 9) else
 (if n < 6099 then
 10 else
 11)) else
 (if n < 9619 then
 (if n < 8266 then
 12 else
 13) else
 (if n < 11447 then
 14 else
 15)))) else
 (if n < 18477 then
 (if n < 17129 then
 (if n < 15491 then
 (if n < 15126 then
 16 else
 17) else
 (if n < 15792 then
 18 else
 19)) else
 (if n < 17511 then
 (if n < 17510 then
 20 else
 21) else
 (if n < 18212 then
 22 else
 23))) else
 (if n < 22833 then
 (if n < 21297 then
 (if n < 19405 then
 24 else
 25) else
 (if n < 22487 then
 26 else
 27)) else
 (if n < 24371 then
 (if n < 24036 then
 28 else
 29) else
 (if n < 24884 then
 30 else
 (if n < 25340 then
 31 else
 32)))))) else
 (if n < 33636 then
 (if n < 30567 then
 (if n < 29441 then
 (if n < 27048 then
 (if n < 26085 then
 33 else
 34) else
 (if n < 27980 then
 35 else
 36)) else
 (if n < 29647 then
 (if n < 29577 then
 37 else
 38) else
 (if n < 30003 then
 39 else
 40))) else
 (if n < 32566 then
 (if n < 31373 then
 (if n < 30667 then
 41 else
 42) else
 (if n < 31880 then
 43 else
 44)) else
 (if n < 32700 then
 (if n < 32647 then
 45 else
 46) else
 (if n < 32910 then
 47 else
 (if n < 32911 then
 48 else
 49))))) else
 (if n < 38179 then
 (if n < 36240 then
 (if n < 35328 then
 (if n < 34050 then
 50 else
 51) else
 (if n < 35885 then
 52 else
 53)) else
 (if n < 37425 then
 (if n < 36641 then
 54 else
 55) else
 (if n < 37863 then
 56 else
 57))) else
 (if n < 40927 then
 (if n < 38419 then
 (if n < 38292 then
 58 else
 59) else
 (if n < 39805 then
 60 else
 61)) else
 (if n < 41456 then
 (if n < 41348 then
 62 else
 63) else
 (if n < 42571 then
 64 else
 (if n < 43297 then
 65 else
 66))))))) else
 (if n < 64148 then
 (if n < 51811 then
 (if n < 47333 then
 (if n < 45292 then
 (if n < 45087 then
 (if n < 44519 then
 67 else
 68) else
 (if n < 45179 then
 69 else
 70)) else
 (if n < 46729 then
 (if n < 45808 then
 71 else
 72) else
 (if n < 46828 then
 73 else
 74))) else
 (if n < 50780 then
 (if n < 48229 then
 (if n < 48005 then
 75 else
 76) else
 (if n < 48983 then
 77 else
 78)) else
 (if n < 51547 then
 (if n < 51466 then
 79 else
 80) else
 (if n < 51600 then
 81 else
 (if n < 51810 then
 82 else
 83))))) else
 (if n < 56979 then
 (if n < 54785 then
 (if n < 52950 then
 (if n < 52536 then
 84 else
 85) else
 (if n < 54228 then
 86 else
 87)) else
 (if n < 55541 then
 (if n < 55140 then
 88 else
 89) else
 (if n < 56325 then
 90 else
 91))) else
 (if n < 57863 then
 (if n < 57671 then
 (if n < 57399 then
 92 else
 93) else
 (if n < 57792 then
 94 else
 95)) else
 (if n < 59464 then
 (if n < 59044 then
 96 else
 97) else
 (if n < 60961 then
 98 else
 (if n < 63040 then
 99 else
 100)))))) else
 (if n < 70827 then
 (if n < 67410 then
 (if n < 66271 then
 (if n < 65280 then
 (if n < 64726 then
 101 else
 102) else
 (if n < 65852 then
 103 else
 104)) else
 (if n < 67161 then
 (if n < 66748 then
 105 else
 106) else
 (if n < 67366 then
 107 else
 108))) else
 (if n < 69410 then
 (if n < 68500 then
 (if n < 67411 then
 109 else
 110) else
 (if n < 68973 then
 111 else
 112)) else
 (if n < 69626 then
 (if n < 69411 then
 113 else
 114) else
 (if n < 69762 then
 115 else
 (if n < 70527 then
 116 else
 117))))) else
 (if n < 75845 then
 (if n < 75083 then
 (if n < 74140 then
 (if n < 73526 then
 118 else
 119) else
 (if n < 74985 then
 120 else
 121)) else
 (if n < 75683 then
 (if n < 75547 then
 122 else
 123) else
 (if n < 75784 then
 124 else
 125))) else
 (if n < 78325 then
 (if n < 77762 then
 (if n < 76720 then
 126 else
 127) else
 (if n < 77933 then
 128 else
 129)) else
 (if n < 79497 then
 (if n < 79029 then
 130 else
 131) else
 (if n < 79734 then
 132 else
 (if n < 80161 then
 133 else
 134)))))))) else
 (if n < 114256 then
 (if n < 95683 then
 (if n < 86587 then
 (if n < 82748 then
 (if n < 81156 then
 (if n < 80608 then
 (if n < 80300 then
 135 else
 136) else
 (if n < 81028 then
 137 else
 138)) else
 (if n < 81703 then
 (if n < 81262 then
 139 else
 140) else
 (if n < 82167 then
 141 else
 142))) else
 (if n < 83433 then
 (if n < 83067 then
 (if n < 82967 then
 143 else
 144) else
 (if n < 83391 then
 145 else
 146)) else
 (if n < 86052 then
 (if n < 84552 then
 147 else
 148) else
 (if n < 86364 then
 149 else
 150)))) else
 (if n < 91400 then
 (if n < 88271 then
 (if n < 87350 then
 (if n < 87077 then
 151 else
 152) else
 (if n < 87750 then
 153 else
 154)) else
 (if n < 89297 then
 (if n < 88308 then
 155 else
 156) else
 (if n < 90479 then
 157 else
 158))) else
 (if n < 94063 then
 (if n < 91720 then
 (if n < 91605 then
 159 else
 160) else
 (if n < 93992 then
 161 else
 162)) else
 (if n < 94364 then
 (if n < 94233 then
 163 else
 164) else
 (if n < 94834 then
 165 else
 (if n < 95161 then
 166 else
 167)))))) else
 (if n < 102445 then
 (if n < 99929 then
 (if n < 97985 then
 (if n < 97291 then
 (if n < 96380 then
 168 else
 169) else
 (if n < 97425 then
 170 else
 171)) else
 (if n < 98284 then
 (if n < 98045 then
 172 else
 173) else
 (if n < 98734 then
 174 else
 175))) else
 (if n < 100979 then
 (if n < 100552 then
 (if n < 100240 then
 176 else
 177) else
 (if n < 100720 then
 178 else
 179)) else
 (if n < 101392 then
 (if n < 101299 then
 180 else
 181) else
 (if n < 101463 then
 182 else
 (if n < 102044 then
 183 else
 184))))) else
 (if n < 107683 then
 (if n < 104764 then
 (if n < 103064 then
 (if n < 102950 then
 185 else
 186) else
 (if n < 103485 then
 187 else
 188)) else
 (if n < 106103 then
 (if n < 105620 then
 189 else
 190) else
 (if n < 107185 then
 191 else
 192))) else
 (if n < 110262 then
 (if n < 109484 then
 (if n < 108450 then
 193 else
 194) else
 (if n < 109928 then
 195 else
 196)) else
 (if n < 111536 then
 (if n < 111134 then
 197 else
 198) else
 (if n < 112261 then
 199 else
 (if n < 112466 then
 200 else
 201))))))) else
 (if n < 133305 then
 (if n < 122110 then
 (if n < 118726 then
 (if n < 116728 then
 (if n < 116336 then
 (if n < 114677 then
 202 else
 203) else
 (if n < 116547 then
 204 else
 205)) else
 (if n < 118077 then
 (if n < 117612 then
 206 else
 207) else
 (if n < 118225 then
 208 else
 209))) else
 (if n < 119927 then
 (if n < 119466 then
 (if n < 119003 then
 210 else
 211) else
 (if n < 119826 then
 212 else
 213)) else
 (if n < 120262 then
 (if n < 120152 then
 214 else
 215) else
 (if n < 120473 then
 216 else
 (if n < 121205 then
 217 else
 218))))) else
 (if n < 128877 then
 (if n < 127144 then
 (if n < 124284 then
 (if n < 122111 then
 219 else
 220) else
 (if n < 126671 then
 221 else
 222)) else
 (if n < 127820 then
 (if n < 127461 then
 223 else
 224) else
 (if n < 128408 then
 225 else
 226))) else
 (if n < 130627 then
 (if n < 129991 then
 (if n < 129236 then
 227 else
 228) else
 (if n < 130127 then
 229 else
 230)) else
 (if n < 131312 then
 (if n < 131120 then
 231 else
 232) else
 (if n < 131412 then
 233 else
 (if n < 133100 then
 234 else
 235)))))) else
 (if n < 141836 then
 (if n < 138141 then
 (if n < 135262 then
 (if n < 135110 then
 (if n < 133787 then
 236 else
 237) else
 (if n < 135111 then
 238 else
 239)) else
 (if n < 135697 then
 (if n < 135467 then
 240 else
 241) else
 (if n < 136344 then
 242 else
 243))) else
 (if n < 139744 then
 (if n < 138484 then
 (if n < 138345 then
 244 else
 245) else
 (if n < 139271 then
 246 else
 247)) else
 (if n < 140420 then
 (if n < 140061 then
 248 else
 249) else
 (if n < 141008 then
 250 else
 (if n < 141477 then
 251 else
 252))))) else
 (if n < 146325 then
 (if n < 143720 then
 (if n < 142727 then
 (if n < 142591 then
 253 else
 254) else
 (if n < 143227 then
 255 else
 256)) else
 (if n < 144012 then
 (if n < 143912 then
 257 else
 258) else
 (if n < 146141 then
 259 else
 260))) else
 (if n < 149844 then
 (if n < 148036 then
 (if n < 146464 then
 261 else
 262) else
 (if n < 148291 then
 263 else
 264)) else
 (if n < 150187 then
 (if n < 149941 then
 265 else
 266) else
 (if n < 150279 then
 267 else
 (if n < 150363 then
 268 else
 269))))))))) else
 (if n < 226566 then
 (if n < 184356 then
 (if n < 167697 then
 (if n < 160425 then
 (if n < 155636 then
 (if n < 153584 then
 (if n < 151783 then
 (if n < 151285 then
 270 else
 271) else
 (if n < 152550 then
 272 else
 273)) else
 (if n < 154362 then
 (if n < 154028 then
 274 else
 275) else
 (if n < 155234 then
 276 else
 277))) else
 (if n < 158161 then
 (if n < 156566 then
 (if n < 156361 then
 278 else
 279) else
 (if n < 157834 then
 280 else
 281)) else
 (if n < 159380 then
 (if n < 158683 then
 282 else
 283) else
 (if n < 160291 then
 284 else
 285)))) else
 (if n < 163720 then
 (if n < 161734 then
 (if n < 161045 then
 (if n < 160985 then
 286 else
 287) else
 (if n < 161284 then
 288 else
 289)) else
 (if n < 163240 then
 (if n < 162929 then
 290 else
 291) else
 (if n < 163552 then
 292 else
 293))) else
 (if n < 164920 then
 (if n < 163984 then
 (if n < 163883 then
 294 else
 295) else
 (if n < 164045 then
 296 else
 297)) else
 (if n < 166133 then
 (if n < 165962 then
 298 else
 299) else
 (if n < 166525 then
 300 else
 (if n < 167229 then
 301 else
 302)))))) else
 (if n < 174261 then
 (if n < 169462 then
 (if n < 168500 then
 (if n < 168361 then
 (if n < 167934 then
 303 else
 304) else
 (if n < 168473 then
 305 else
 306)) else
 (if n < 169228 then
 (if n < 168808 then
 307 else
 308) else
 (if n < 169356 then
 309 else
 310))) else
 (if n < 171826 then
 (if n < 170140 then
 (if n < 169903 then
 311 else
 312) else
 (if n < 171248 then
 313 else
 314)) else
 (if n < 172952 then
 (if n < 172380 then
 315 else
 316) else
 (if n < 173371 then
 317 else
 (if n < 173848 then
 318 else
 319))))) else
 (if n < 176892 then
 (if n < 175600 then
 (if n < 174510 then
 (if n < 174466 then
 320 else
 321) else
 (if n < 174511 then
 322 else
 323)) else
 (if n < 176463 then
 (if n < 176073 then
 324 else
 325) else
 (if n < 176779 then
 326 else
 327))) else
 (if n < 179948 then
 (if n < 178405 then
 (if n < 177019 then
 328 else
 329) else
 (if n < 179527 then
 330 else
 331)) else
 (if n < 181171 then
 (if n < 180056 then
 332 else
 333) else
 (if n < 181897 then
 334 else
 (if n < 183373 then
 335 else
 336))))))) else
 (if n < 203503 then
 (if n < 194467 then
 (if n < 189448 then
 (if n < 185812 then
 (if n < 184603 then
 (if n < 184456 then
 337 else
 338) else
 (if n < 185380 then
 339 else
 340)) else
 (if n < 187645 then
 (if n < 187019 then
 341 else
 342) else
 (if n < 189140 then
 343 else
 344))) else
 (if n < 193241 then
 (if n < 190848 then
 (if n < 189885 then
 345 else
 346) else
 (if n < 191780 then
 347 else
 348)) else
 (if n < 193447 then
 (if n < 193377 then
 349 else
 350) else
 (if n < 193803 then
 351 else
 (if n < 194367 then
 352 else
 353))))) else
 (if n < 197450 then
 (if n < 195892 then
 (if n < 195479 then
 (if n < 195173 then
 354 else
 355) else
 (if n < 195799 then
 356 else
 357)) else
 (if n < 196544 then
 (if n < 195963 then
 358 else
 359) else
 (if n < 196945 then
 360 else
 361))) else
 (if n < 200120 then
 (if n < 197985 then
 (if n < 197564 then
 362 else
 363) else
 (if n < 199264 then
 364 else
 365)) else
 (if n < 202273 then
 (if n < 200603 then
 366 else
 367) else
 (if n < 203256 then
 368 else
 (if n < 203356 then
 369 else
 370)))))) else
 (if n < 214705 then
 (if n < 210710 then
 (if n < 206545 then
 (if n < 204712 then
 (if n < 204280 then
 371 else
 372) else
 (if n < 205919 then
 373 else
 374)) else
 (if n < 208905 then
 (if n < 208700 then
 375 else
 376) else
 (if n < 209387 then
 377 else
 378))) else
 (if n < 211297 then
 (if n < 210862 then
 (if n < 210711 then
 379 else
 380) else
 (if n < 211067 then
 381 else
 382)) else
 (if n < 213741 then
 (if n < 211944 then
 383 else
 384) else
 (if n < 213945 then
 385 else
 (if n < 214084 then
 386 else
 387))))) else
 (if n < 221777 then
 (if n < 219336 then
 (if n < 217787 then
 (if n < 216597 then
 388 else
 389) else
 (if n < 218133 then
 390 else
 391)) else
 (if n < 220184 then
 (if n < 219671 then
 392 else
 393) else
 (if n < 221356 then
 394 else
 395))) else
 (if n < 224712 then
 (if n < 223647 then
 (if n < 223436 then
 396 else
 397) else
 (if n < 223828 then
 398 else
 399)) else
 (if n < 225325 then
 (if n < 225177 then
 400 else
 401) else
 (if n < 225826 then
 402 else
 (if n < 226103 then
 403 else
 404)))))))) else
 (if n < 270383 then
 (if n < 250847 then
 (if n < 238141 then
 (if n < 232412 then
 (if n < 229992 then
 (if n < 229326 then
 (if n < 227173 then
 405 else
 406) else
 (if n < 229691 then
 407 else
 408)) else
 (if n < 231710 then
 (if n < 231329 then
 409 else
 410) else
 (if n < 231711 then
 411 else
 412))) else
 (if n < 234664 then
 (if n < 234341 then
 (if n < 232677 then
 413 else
 414) else
 (if n < 234525 then
 415 else
 416)) else
 (if n < 236491 then
 (if n < 236236 then
 417 else
 418) else
 (if n < 238044 then
 419 else
 420)))) else
 (if n < 239962 then
 (if n < 238652 then
 (if n < 238479 then
 (if n < 238387 then
 421 else
 422) else
 (if n < 238563 then
 423 else
 424)) else
 (if n < 239627 then
 (if n < 239526 then
 425 else
 426) else
 (if n < 239852 then
 427 else
 428))) else
 (if n < 241811 then
 (if n < 240905 then
 (if n < 240173 then
 429 else
 430) else
 (if n < 241810 then
 431 else
 432)) else
 (if n < 247250 then
 (if n < 243984 then
 433 else
 434) else
 (if n < 247666 then
 435 else
 (if n < 249019 then
 436 else
 437)))))) else
 (if n < 261129 then
 (if n < 254728 then
 (if n < 253079 then
 (if n < 252419 then
 (if n < 252263 then
 438 else
 439) else
 (if n < 252987 then
 440 else
 441)) else
 (if n < 253708 then
 (if n < 253192 then
 442 else
 443) else
 (if n < 254629 then
 444 else
 445))) else
 (if n < 256883 then
 (if n < 255905 then
 (if n < 255233 then
 446 else
 447) else
 (if n < 256129 then
 448 else
 449)) else
 (if n < 258580 then
 (if n < 258300 then
 450 else
 451) else
 (if n < 258934 then
 452 else
 (if n < 260408 then
 453 else
 454))))) else
 (if n < 264710 then
 (if n < 262708 then
 (if n < 262599 then
 (if n < 261540 then
 455 else
 456) else
 (if n < 262603 then
 457 else
 458)) else
 (if n < 264183 then
 (if n < 263025 then
 459 else
 460) else
 (if n < 264399 then
 461 else
 462))) else
 (if n < 265827 then
 (if n < 264926 then
 (if n < 264711 then
 463 else
 464) else
 (if n < 265062 then
 465 else
 466)) else
 (if n < 268826 then
 (if n < 266127 then
 467 else
 468) else
 (if n < 269440 then
 469 else
 (if n < 270285 then
 470 else
 471))))))) else
 (if n < 284663 then
 (if n < 278544 then
 (if n < 274420 then
 (if n < 271997 then
 (if n < 270971 then
 (if n < 270847 then
 472 else
 473) else
 (if n < 271008 then
 474 else
 475)) else
 (if n < 274100 then
 (if n < 273179 then
 476 else
 477) else
 (if n < 274305 then
 478 else
 479))) else
 (if n < 277064 then
 (if n < 276763 then
 (if n < 276692 then
 480 else
 481) else
 (if n < 276933 then
 482 else
 483)) else
 (if n < 277787 then
 (if n < 277466 then
 484 else
 485) else
 (if n < 277833 then
 486 else
 (if n < 278247 then
 487 else
 488))))) else
 (if n < 281545 then
 (if n < 279319 then
 (if n < 278934 then
 (if n < 278799 then
 489 else
 490) else
 (if n < 279241 then
 491 else
 492)) else
 (if n < 280828 then
 (if n < 280297 then
 493 else
 494) else
 (if n < 281399 then
 495 else
 496))) else
 (if n < 283312 then
 (if n < 281956 then
 (if n < 281691 then
 497 else
 498) else
 (if n < 282819 then
 499 else
 500)) else
 (if n < 284199 then
 (if n < 283779 then
 501 else
 502) else
 (if n < 284471 then
 503 else
 (if n < 284592 then
 504 else
 505)))))) else
 (if n < 294291 then
 (if n < 291144 then
 (if n < 290066 then
 (if n < 286264 then
 (if n < 285844 then
 506 else
 507) else
 (if n < 287761 then
 508 else
 509)) else
 (if n < 290433 then
 (if n < 290387 then
 510 else
 511) else
 (if n < 290847 then
 512 else
 513))) else
 (if n < 291919 then
 (if n < 291534 then
 (if n < 291399 then
 514 else
 515) else
 (if n < 291841 then
 516 else
 517)) else
 (if n < 293428 then
 (if n < 292897 then
 518 else
 519) else
 (if n < 293999 then
 520 else
 (if n < 294145 then
 521 else
 522))))) else
 (if n < 297591 then
 (if n < 296367 then
 (if n < 295419 then
 (if n < 294556 then
 523 else
 524) else
 (if n < 295912 then
 525 else
 526)) else
 (if n < 297167 then
 (if n < 296948 then
 527 else
 528) else
 (if n < 297267 then
 529 else
 530))) else
 (if n < 300564 then
 (if n < 298752 then
 (if n < 297633 then
 531 else
 532) else
 (if n < 300252 then
 533 else
 534)) else
 (if n < 301277 then
 (if n < 300787 then
 535 else
 536) else
 (if n < 301550 then
 537 else
 (if n < 301950 then
 538 else
 539)))))))))) else
 (if n < 453880 then
 (if n < 378373 then
 (if n < 335656 then
 (if n < 319134 then
 (if n < 312185 then
 (if n < 307561 then
 (if n < 305228 then
 (if n < 303750 then
 (if n < 302983 then
 540 else
 541) else
 (if n < 304784 then
 542 else
 543)) else
 (if n < 306434 then
 (if n < 305562 then
 544 else
 545) else
 (if n < 306836 then
 546 else
 547))) else
 (if n < 309883 then
 (if n < 309034 then
 (if n < 307766 then
 548 else
 549) else
 (if n < 309361 then
 550 else
 551)) else
 (if n < 311491 then
 (if n < 310580 then
 552 else
 553) else
 (if n < 311625 then
 554 else
 555)))) else
 (if n < 315083 then
 (if n < 314129 then
 (if n < 312484 then
 (if n < 312245 then
 556 else
 557) else
 (if n < 312934 then
 558 else
 559)) else
 (if n < 314752 then
 (if n < 314440 then
 560 else
 561) else
 (if n < 314920 then
 562 else
 563))) else
 (if n < 317162 then
 (if n < 315245 then
 (if n < 315184 then
 564 else
 565) else
 (if n < 316120 then
 566 else
 567)) else
 (if n < 317725 then
 (if n < 317333 then
 568 else
 569) else
 (if n < 318429 then
 570 else
 (if n < 318897 then
 571 else
 572)))))) else
 (if n < 325666 then
 (if n < 321103 then
 (if n < 320008 then
 (if n < 319673 then
 (if n < 319561 then
 573 else
 574) else
 (if n < 319700 then
 575 else
 576)) else
 (if n < 320556 then
 (if n < 320428 then
 577 else
 578) else
 (if n < 320662 then
 579 else
 580))) else
 (if n < 323580 then
 (if n < 322448 then
 (if n < 321340 then
 581 else
 582) else
 (if n < 323026 then
 583 else
 584)) else
 (if n < 324571 then
 (if n < 324152 then
 585 else
 586) else
 (if n < 325048 then
 587 else
 (if n < 325461 then
 588 else
 589))))) else
 (if n < 328219 then
 (if n < 327273 then
 (if n < 325711 then
 (if n < 325710 then
 590 else
 591) else
 (if n < 326800 then
 592 else
 593)) else
 (if n < 327979 then
 (if n < 327663 then
 594 else
 595) else
 (if n < 328092 then
 596 else
 597))) else
 (if n < 331256 then
 (if n < 330727 then
 (if n < 329605 then
 598 else
 599) else
 (if n < 331148 then
 600 else
 601)) else
 (if n < 333097 then
 (if n < 332371 then
 602 else
 603) else
 (if n < 334573 then
 604 else
 (if n < 335556 then
 605 else
 606))))))) else
 (if n < 355480 then
 (if n < 346373 then
 (if n < 341085 then
 (if n < 338219 then
 (if n < 336580 then
 (if n < 335803 then
 607 else
 608) else
 (if n < 337012 then
 609 else
 610)) else
 (if n < 340340 then
 (if n < 338845 then
 611 else
 612) else
 (if n < 340648 then
 613 else
 614))) else
 (if n < 344577 then
 (if n < 342980 then
 (if n < 342048 then
 615 else
 616) else
 (if n < 344441 then
 617 else
 618)) else
 (if n < 345003 then
 (if n < 344647 then
 619 else
 620) else
 (if n < 345567 then
 621 else
 (if n < 345667 then
 622 else
 623))))) else
 (if n < 348764 then
 (if n < 347163 then
 (if n < 346999 then
 (if n < 346679 then
 624 else
 625) else
 (if n < 347092 then
 626 else
 627)) else
 (if n < 348145 then
 (if n < 347744 then
 628 else
 629) else
 (if n < 348650 then
 630 else
 631))) else
 (if n < 351803 then
 (if n < 350464 then
 (if n < 349185 then
 632 else
 633) else
 (if n < 351320 then
 634 else
 635)) else
 (if n < 354456 then
 (if n < 353473 then
 636 else
 637) else
 (if n < 354556 then
 638 else
 (if n < 354703 then
 639 else
 640)))))) else
 (if n < 367797 then
 (if n < 361911 then
 (if n < 359900 then
 (if n < 357119 then
 (if n < 355912 then
 641 else
 642) else
 (if n < 357745 then
 643 else
 644)) else
 (if n < 360587 then
 (if n < 360105 then
 645 else
 646) else
 (if n < 361910 then
 647 else
 648))) else
 (if n < 363144 then
 (if n < 362267 then
 (if n < 362062 then
 649 else
 650) else
 (if n < 362497 then
 651 else
 652)) else
 (if n < 365145 then
 (if n < 364941 then
 653 else
 654) else
 (if n < 365284 then
 655 else
 (if n < 365905 then
 656 else
 657))))) else
 (if n < 374636 then
 (if n < 370871 then
 (if n < 369333 then
 (if n < 368987 then
 658 else
 659) else
 (if n < 370536 then
 660 else
 661)) else
 (if n < 372556 then
 (if n < 371384 then
 662 else
 663) else
 (if n < 372977 then
 664 else
 665))) else
 (if n < 376377 then
 (if n < 375028 then
 (if n < 374847 then
 666 else
 667) else
 (if n < 375912 then
 668 else
 669)) else
 (if n < 377026 then
 (if n < 376525 then
 670 else
 671) else
 (if n < 377303 then
 672 else
 (if n < 377766 then
 673 else
 674)))))))) else
 (if n < 422047 then
 (if n < 403463 then
 (if n < 389587 then
 (if n < 383877 then
 (if n < 382529 then
 (if n < 380891 then
 (if n < 380526 then
 675 else
 676) else
 (if n < 381192 then
 677 else
 678)) else
 (if n < 382911 then
 (if n < 382910 then
 679 else
 680) else
 (if n < 383612 then
 681 else
 682))) else
 (if n < 387436 then
 (if n < 385725 then
 (if n < 385541 then
 683 else
 684) else
 (if n < 385864 then
 685 else
 686)) else
 (if n < 389244 then
 (if n < 387691 then
 687 else
 688) else
 (if n < 389341 then
 689 else
 690)))) else
 (if n < 391373 then
 (if n < 390726 then
 (if n < 389763 then
 (if n < 389679 then
 691 else
 692) else
 (if n < 389852 then
 693 else
 694)) else
 (if n < 391052 then
 (if n < 390827 then
 695 else
 696) else
 (if n < 391162 then
 697 else
 698))) else
 (if n < 395184 then
 (if n < 393010 then
 (if n < 392105 then
 699 else
 700) else
 (if n < 393011 then
 701 else
 702)) else
 (if n < 398866 then
 (if n < 398450 then
 703 else
 704) else
 (if n < 400219 then
 705 else
 (if n < 402047 then
 706 else
 707)))))) else
 (if n < 412740 then
 (if n < 406433 then
 (if n < 404392 then
 (if n < 404187 then
 (if n < 403619 then
 708 else
 709) else
 (if n < 404279 then
 710 else
 711)) else
 (if n < 405829 then
 (if n < 404908 then
 712 else
 713) else
 (if n < 405928 then
 714 else
 715))) else
 (if n < 409500 then
 (if n < 407329 then
 (if n < 407105 then
 716 else
 717) else
 (if n < 408083 then
 718 else
 719)) else
 (if n < 410134 then
 (if n < 409780 then
 720 else
 721) else
 (if n < 411608 then
 722 else
 (if n < 412329 then
 723 else
 724))))) else
 (if n < 415911 then
 (if n < 414225 then
 (if n < 413803 then
 (if n < 413799 then
 725 else
 726) else
 (if n < 413908 then
 727 else
 728)) else
 (if n < 415599 then
 (if n < 415383 then
 729 else
 730) else
 (if n < 415910 then
 731 else
 732))) else
 (if n < 417327 then
 (if n < 416262 then
 (if n < 416126 then
 733 else
 734) else
 (if n < 417027 then
 735 else
 736)) else
 (if n < 420640 then
 (if n < 420026 then
 737 else
 738) else
 (if n < 421485 then
 739 else
 (if n < 421583 then
 740 else
 741))))))) else
 (if n < 437044 then
 (if n < 429999 then
 (if n < 427892 then
 (if n < 424379 then
 (if n < 422208 then
 (if n < 422171 then
 742 else
 743) else
 (if n < 423197 then
 744 else
 745)) else
 (if n < 425505 then
 (if n < 425300 then
 746 else
 747) else
 (if n < 425620 then
 748 else
 749))) else
 (if n < 428666 then
 (if n < 428133 then
 (if n < 427963 then
 750 else
 751) else
 (if n < 428264 then
 752 else
 753)) else
 (if n < 429033 then
 (if n < 428987 then
 754 else
 755) else
 (if n < 429447 then
 756 else
 (if n < 429744 then
 757 else
 758))))) else
 (if n < 432891 then
 (if n < 431497 then
 (if n < 430441 then
 (if n < 430134 then
 759 else
 760) else
 (if n < 430519 then
 761 else
 762)) else
 (if n < 432599 then
 (if n < 432028 then
 763 else
 764) else
 (if n < 432745 then
 765 else
 766))) else
 (if n < 434979 then
 (if n < 434019 then
 (if n < 433156 then
 767 else
 768) else
 (if n < 434512 then
 769 else
 770)) else
 (if n < 435671 then
 (if n < 435399 then
 771 else
 772) else
 (if n < 435792 then
 773 else
 (if n < 435863 then
 774 else
 775)))))) else
 (if n < 445756 then
 (if n < 442599 then
 (if n < 441587 then
 (if n < 438961 then
 (if n < 437464 then
 776 else
 777) else
 (if n < 441266 then
 778 else
 779)) else
 (if n < 442047 then
 (if n < 441633 then
 780 else
 781) else
 (if n < 442344 then
 782 else
 783))) else
 (if n < 444097 then
 (if n < 443041 then
 (if n < 442734 then
 784 else
 785) else
 (if n < 443119 then
 786 else
 787)) else
 (if n < 445199 then
 (if n < 444628 then
 788 else
 789) else
 (if n < 445345 then
 790 else
 (if n < 445491 then
 791 else
 792))))) else
 (if n < 448833 then
 (if n < 448148 then
 (if n < 447112 then
 (if n < 446619 then
 793 else
 794) else
 (if n < 447567 then
 795 else
 796)) else
 (if n < 448467 then
 (if n < 448367 then
 797 else
 798) else
 (if n < 448791 then
 799 else
 800))) else
 (if n < 451987 then
 (if n < 451452 then
 (if n < 449952 then
 801 else
 802) else
 (if n < 451764 then
 803 else
 804)) else
 (if n < 452750 then
 (if n < 452477 then
 805 else
 806) else
 (if n < 453150 then
 807 else
 (if n < 453600 then
 808 else
 809))))))))) else
 (if n < 533900 then
 (if n < 498119 then
 (if n < 479685 then
 (if n < 468726 then
 (if n < 458325 then
 (if n < 456840 then
 (if n < 455708 then
 (if n < 454234 then
 810 else
 811) else
 (if n < 456429 then
 812 else
 813)) else
 (if n < 457903 then
 (if n < 457899 then
 814 else
 815) else
 (if n < 458008 then
 816 else
 817))) else
 (if n < 461866 then
 (if n < 459699 then
 (if n < 459483 then
 818 else
 819) else
 (if n < 461450 then
 820 else
 821)) else
 (if n < 465047 then
 (if n < 463219 then
 822 else
 823) else
 (if n < 466573 then
 824 else
 825)))) else
 (if n < 473005 then
 (if n < 471110 then
 (if n < 469392 then
 (if n < 469091 then
 826 else
 827) else
 (if n < 470729 then
 828 else
 829)) else
 (if n < 471812 then
 (if n < 471111 then
 830 else
 831) else
 (if n < 472077 then
 832 else
 833))) else
 (if n < 477636 then
 (if n < 476087 then
 (if n < 474897 then
 834 else
 835) else
 (if n < 476433 then
 836 else
 837)) else
 (if n < 478484 then
 (if n < 477971 then
 838 else
 839) else
 (if n < 478940 then
 840 else
 (if n < 479248 then
 841 else
 842)))))) else
 (if n < 487650 then
 (if n < 484267 then
 (if n < 483177 then
 (if n < 481580 then
 (if n < 480648 then
 843 else
 844) else
 (if n < 483041 then
 845 else
 846)) else
 (if n < 483603 then
 (if n < 483247 then
 847 else
 848) else
 (if n < 484167 then
 849 else
 850))) else
 (if n < 486247 then
 (if n < 485480 then
 (if n < 484973 then
 851 else
 852) else
 (if n < 486166 then
 853 else
 854)) else
 (if n < 486510 then
 (if n < 486300 then
 855 else
 856) else
 (if n < 486511 then
 857 else
 (if n < 487236 then
 858 else
 859))))) else
 (if n < 491892 then
 (if n < 490241 then
 (if n < 489485 then
 (if n < 488928 then
 860 else
 861) else
 (if n < 489840 then
 862 else
 863)) else
 (if n < 491463 then
 (if n < 491025 then
 864 else
 865) else
 (if n < 491779 then
 866 else
 867))) else
 (if n < 494948 then
 (if n < 493405 then
 (if n < 492019 then
 868 else
 869) else
 (if n < 494527 then
 870 else
 871)) else
 (if n < 496171 then
 (if n < 495056 then
 872 else
 873) else
 (if n < 496897 then
 874 else
 (if n < 497963 then
 875 else
 876))))))) else
 (if n < 518326 then
 (if n < 506136 then
 (if n < 501605 then
 (if n < 499408 then
 (if n < 498779 then
 (if n < 498687 then
 877 else
 878) else
 (if n < 498892 then
 879 else
 880)) else
 (if n < 500428 then
 (if n < 500329 then
 881 else
 882) else
 (if n < 500933 then
 883 else
 884))) else
 (if n < 505066 then
 (if n < 502583 then
 (if n < 501829 then
 885 else
 886) else
 (if n < 504380 then
 887 else
 888)) else
 (if n < 505200 then
 (if n < 505147 then
 889 else
 890) else
 (if n < 505410 then
 891 else
 (if n < 505411 then
 892 else
 893))))) else
 (if n < 510999 then
 (if n < 508740 then
 (if n < 507828 then
 (if n < 506550 then
 894 else
 895) else
 (if n < 508385 then
 896 else
 897)) else
 (if n < 509925 then
 (if n < 509141 then
 898 else
 899) else
 (if n < 510579 then
 900 else
 901))) else
 (if n < 512644 then
 (if n < 511392 then
 (if n < 511271 then
 902 else
 903) else
 (if n < 511463 then
 904 else
 905)) else
 (if n < 514561 then
 (if n < 513064 then
 906 else
 907) else
 (if n < 516640 then
 908 else
 (if n < 517748 then
 909 else
 910)))))) else
 (if n < 527126 then
 (if n < 521011 then
 (if n < 520348 then
 (if n < 519452 then
 (if n < 518880 then
 911 else
 912) else
 (if n < 519871 then
 913 else
 914)) else
 (if n < 520966 then
 (if n < 520761 then
 915 else
 916) else
 (if n < 521010 then
 917 else
 918))) else
 (if n < 523011 then
 (if n < 522573 then
 (if n < 522100 then
 919 else
 920) else
 (if n < 523010 then
 921 else
 922)) else
 (if n < 523362 then
 (if n < 523226 then
 923 else
 924) else
 (if n < 524127 then
 925 else
 (if n < 524427 then
 926 else
 927))))) else
 (if n < 530320 then
 (if n < 529147 then
 (if n < 528585 then
 (if n < 527740 then
 928 else
 929) else
 (if n < 528683 then
 930 else
 931)) else
 (if n < 529384 then
 (if n < 529283 then
 932 else
 933) else
 (if n < 529445 then
 934 else
 935))) else
 (if n < 532629 then
 (if n < 531533 then
 (if n < 531362 then
 936 else
 937) else
 (if n < 531925 then
 938 else
 939)) else
 (if n < 533334 then
 (if n < 533097 then
 940 else
 941) else
 (if n < 533761 then
 942 else
 (if n < 533873 then
 943 else
 944)))))))) else
 (if n < 568277 then
 (if n < 549980 then
 (if n < 540677 then
 (if n < 536567 then
 (if n < 534862 then
 (if n < 534628 then
 (if n < 534208 then
 945 else
 946) else
 (if n < 534756 then
 947 else
 948)) else
 (if n < 535767 then
 (if n < 535303 then
 949 else
 950) else
 (if n < 536348 then
 951 else
 952))) else
 (if n < 538152 then
 (if n < 536991 then
 (if n < 536667 then
 953 else
 954) else
 (if n < 537033 then
 955 else
 956)) else
 (if n < 539964 then
 (if n < 539652 then
 957 else
 958) else
 (if n < 540187 then
 959 else
 960)))) else
 (if n < 545205 then
 (if n < 541908 then
 (if n < 541350 then
 (if n < 540950 then
 961 else
 962) else
 (if n < 541871 then
 963 else
 964)) else
 (if n < 544079 then
 (if n < 542897 then
 965 else
 966) else
 (if n < 545000 then
 967 else
 968))) else
 (if n < 547833 then
 (if n < 547592 then
 (if n < 545320 then
 969 else
 970) else
 (if n < 547663 then
 971 else
 972)) else
 (if n < 548434 then
 (if n < 547964 then
 973 else
 974) else
 (if n < 548761 then
 975 else
 (if n < 549283 then
 976 else
 977)))))) else
 (if n < 556550 then
 (if n < 553840 then
 (if n < 551645 then
 (if n < 551025 then
 (if n < 550891 then
 978 else
 979) else
 (if n < 551585 then
 980 else
 981)) else
 (if n < 552334 then
 (if n < 551884 then
 982 else
 983) else
 (if n < 553529 then
 984 else
 985))) else
 (if n < 554899 then
 (if n < 554320 then
 (if n < 554152 then
 986 else
 987) else
 (if n < 554579 then
 988 else
 989)) else
 (if n < 555063 then
 (if n < 554992 then
 990 else
 991) else
 (if n < 555644 then
 992 else
 (if n < 556045 then
 993 else
 994))))) else
 (if n < 562050 then
 (if n < 559220 then
 (if n < 557085 then
 (if n < 556664 then
 995 else
 996) else
 (if n < 558364 then
 997 else
 998)) else
 (if n < 560785 then
 (if n < 559703 then
 999 else
 1000) else
 (if n < 561283 then
 1001 else
 1002))) else
 (if n < 564734 then
 (if n < 563528 then
 (if n < 563084 then
 1003 else
 1004) else
 (if n < 563862 then
 1005 else
 1006)) else
 (if n < 565861 then
 (if n < 565136 then
 1007 else
 1008) else
 (if n < 566066 then
 1009 else
 (if n < 567856 then
 1010 else
 1011))))))) else
 (if n < 587387 then
 (if n < 575711 then
 (if n < 572603 then
 (if n < 571212 then
 (if n < 570147 then
 (if n < 569936 then
 1012 else
 1013) else
 (if n < 570328 then
 1014 else
 1015)) else
 (if n < 571825 then
 (if n < 571677 then
 1016 else
 1017) else
 (if n < 572326 then
 1018 else
 1019))) else
 (if n < 573752 then
 (if n < 573426 then
 (if n < 573066 then
 1020 else
 1021) else
 (if n < 573527 then
 1022 else
 1023)) else
 (if n < 574073 then
 (if n < 573862 then
 1024 else
 1025) else
 (if n < 574805 then
 1026 else
 (if n < 575710 then
 1027 else
 1028))))) else
 (if n < 582836 then
 (if n < 581061 then
 (if n < 580271 then
 (if n < 577884 then
 1029 else
 1030) else
 (if n < 580744 then
 1031 else
 1032)) else
 (if n < 582008 then
 (if n < 581420 then
 1033 else
 1034) else
 (if n < 582477 then
 1035 else
 1036))) else
 (if n < 584720 then
 (if n < 583727 then
 (if n < 583591 then
 1037 else
 1038) else
 (if n < 584227 then
 1039 else
 1040)) else
 (if n < 585012 then
 (if n < 584912 then
 1041 else
 1042) else
 (if n < 586700 then
 1043 else
 (if n < 586905 then
 1044 else
 1045)))))) else
 (if n < 596191 then
 (if n < 591945 then
 (if n < 589067 then
 (if n < 588711 then
 (if n < 588710 then
 1046 else
 1047) else
 (if n < 588862 then
 1048 else
 1049)) else
 (if n < 589944 then
 (if n < 589297 then
 1050 else
 1051) else
 (if n < 591741 then
 1052 else
 1053))) else
 (if n < 593661 then
 (if n < 592871 then
 (if n < 592084 then
 1054 else
 1055) else
 (if n < 593344 then
 1056 else
 1057)) else
 (if n < 594608 then
 (if n < 594020 then
 1058 else
 1059) else
 (if n < 595077 then
 1060 else
 (if n < 595436 then
 1061 else
 1062))))) else
 (if n < 600064 then
 (if n < 597512 then
 (if n < 596827 then
 (if n < 596327 then
 1063 else
 1064) else
 (if n < 597320 then
 1065 else
 1066)) else
 (if n < 599741 then
 (if n < 597612 then
 1067 else
 1068) else
 (if n < 599925 then
 1069 else
 1070))) else
 (if n < 603541 then
 (if n < 601891 then
 (if n < 601636 then
 1071 else
 1072) else
 (if n < 603444 then
 1073 else
 1074)) else
 (if n < 603879 then
 (if n < 603787 then
 1075 else
 1076) else
 (if n < 603963 then
 1077 else
 (if n < 604052 then
 1078 else
 1079)))))))))))

def orbitDecode (x : Index) : Nat :=
  let n := indexCode x
 (if n < 322852 then
 (if n < 171422 then
 (if n < 84842 then
 (if n < 40202 then
 (if n < 16315 then
 (if n < 6234 then
 (if n < 3624 then
 (if n < 1542 then
 (if n < 903 then
 0 else
 1) else
 (if n < 2438 then
 2 else
 3)) else
 (if n < 5306 then
 (if n < 4533 then
 4 else
 5) else
 (if n < 6037 then
 6 else
 7))) else
 (if n < 11629 then
 (if n < 6338 then
 (if n < 6311 then
 8 else
 9) else
 (if n < 9100 then
 10 else
 11)) else
 (if n < 13517 then
 (if n < 12609 then
 12 else
 13) else
 (if n < 13920 then
 14 else
 (if n < 14101 then
 15 else
 16))))) else
 (if n < 25208 then
 (if n < 20511 then
 (if n < 19152 then
 (if n < 17734 then
 17 else
 18) else
 (if n < 19818 then
 19 else
 20)) else
 (if n < 21000 then
 (if n < 20603 then
 21 else
 22) else
 (if n < 21117 then
 23 else
 (if n < 22325 then
 24 else
 25)))) else
 (if n < 31607 then
 (if n < 30530 then
 (if n < 25451 then
 26 else
 27) else
 (if n < 30813 then
 28 else
 29)) else
 (if n < 35112 then
 (if n < 33624 then
 30 else
 31) else
 (if n < 35918 then
 32 else
 (if n < 36938 then
 33 else
 34)))))) else
 (if n < 56913 then
 (if n < 50443 then
 (if n < 44100 then
 (if n < 41348 then
 (if n < 40807 then
 35 else
 36) else
 (if n < 43409 then
 37 else
 38)) else
 (if n < 49225 then
 (if n < 46143 then
 39 else
 40) else
 (if n < 50439 then
 41 else
 42))) else
 (if n < 51908 then
 (if n < 51142 then
 (if n < 50705 then
 43 else
 44) else
 (if n < 51704 then
 45 else
 46)) else
 (if n < 52428 then
 (if n < 52011 then
 47 else
 48) else
 (if n < 56700 then
 49 else
 (if n < 56701 then
 50 else
 51))))) else
 (if n < 70810 then
 (if n < 60929 then
 (if n < 57828 then
 (if n < 57748 then
 52 else
 53) else
 (if n < 58651 then
 54 else
 55)) else
 (if n < 64509 then
 (if n < 62134 then
 56 else
 57) else
 (if n < 64952 then
 58 else
 (if n < 68610 then
 59 else
 60)))) else
 (if n < 79005 then
 (if n < 74002 then
 (if n < 71018 then
 61 else
 62) else
 (if n < 76906 then
 63 else
 64)) else
 (if n < 83248 then
 (if n < 79148 then
 65 else
 66) else
 (if n < 83939 then
 67 else
 (if n < 84506 then
 68 else
 69))))))) else
 (if n < 131643 then
 (if n < 109111 then
 (if n < 95510 then
 (if n < 89829 then
 (if n < 86220 then
 (if n < 86033 then
 70 else
 71) else
 (if n < 86905 then
 72 else
 73)) else
 (if n < 90839 then
 (if n < 90716 then
 74 else
 75) else
 (if n < 94800 then
 76 else
 77))) else
 (if n < 99138 then
 (if n < 96333 then
 (if n < 96143 then
 78 else
 79) else
 (if n < 96407 then
 80 else
 81)) else
 (if n < 102439 then
 (if n < 101907 then
 82 else
 83) else
 (if n < 105603 then
 84 else
 (if n < 109000 then
 85 else
 86))))) else
 (if n < 120407 then
 (if n < 113009 then
 (if n < 109706 then
 (if n < 109318 then
 87 else
 88) else
 (if n < 111917 then
 89 else
 90)) else
 (if n < 116402 then
 (if n < 114439 then
 91 else
 92) else
 (if n < 116825 then
 93 else
 (if n < 118938 then
 94 else
 95)))) else
 (if n < 127938 then
 (if n < 125301 then
 (if n < 123212 then
 96 else
 97) else
 (if n < 126300 then
 98 else
 99)) else
 (if n < 129425 then
 (if n < 127942 then
 100 else
 101) else
 (if n < 129713 then
 102 else
 (if n < 131114 then
 103 else
 104)))))) else
 (if n < 152530 then
 (if n < 141118 then
 (if n < 134922 then
 (if n < 133621 then
 (if n < 132628 then
 105 else
 106) else
 (if n < 134817 then
 107 else
 108)) else
 (if n < 137013 then
 (if n < 136507 then
 109 else
 110) else
 (if n < 137200 then
 111 else
 112))) else
 (if n < 145939 then
 (if n < 142520 then
 (if n < 141211 then
 113 else
 114) else
 (if n < 145912 then
 115 else
 116)) else
 (if n < 150811 then
 (if n < 146814 then
 117 else
 118) else
 (if n < 151402 then
 119 else
 (if n < 152243 then
 120 else
 121))))) else
 (if n < 163800 then
 (if n < 159703 then
 (if n < 155928 then
 (if n < 153613 then
 122 else
 123) else
 (if n < 156839 then
 124 else
 125)) else
 (if n < 160905 then
 (if n < 160130 then
 126 else
 127) else
 (if n < 162317 then
 128 else
 (if n < 162652 then
 129 else
 130)))) else
 (if n < 165517 then
 (if n < 165342 then
 (if n < 165311 then
 131 else
 132) else
 (if n < 165352 then
 133 else
 134)) else
 (if n < 167216 then
 (if n < 166100 then
 135 else
 136) else
 (if n < 170500 then
 137 else
 (if n < 171124 then
 138 else
 139)))))))) else
 (if n < 249212 then
 (if n < 211548 then
 (if n < 194016 then
 (if n < 183522 then
 (if n < 179112 then
 (if n < 174903 then
 (if n < 173528 then
 140 else
 141) else
 (if n < 176039 then
 142 else
 143)) else
 (if n < 181318 then
 (if n < 179413 then
 144 else
 145) else
 (if n < 181334 then
 146 else
 147))) else
 (if n < 188728 then
 (if n < 187534 then
 (if n < 183842 then
 148 else
 149) else
 (if n < 187928 then
 150 else
 151)) else
 (if n < 190329 then
 (if n < 189822 then
 152 else
 153) else
 (if n < 190513 then
 154 else
 (if n < 192918 then
 155 else
 156))))) else
 (if n < 205806 then
 (if n < 198210 then
 (if n < 197309 then
 (if n < 194228 then
 157 else
 158) else
 (if n < 197929 then
 159 else
 160)) else
 (if n < 201608 then
 (if n < 201204 then
 161 else
 162) else
 (if n < 201609 then
 163 else
 (if n < 202624 then
 164 else
 165)))) else
 (if n < 207433 then
 (if n < 206403 then
 (if n < 206033 then
 166 else
 167) else
 (if n < 207424 then
 168 else
 169)) else
 (if n < 208943 then
 (if n < 207911 then
 170 else
 171) else
 (if n < 209407 then
 172 else
 (if n < 211325 then
 173 else
 174)))))) else
 (if n < 233133 then
 (if n < 219352 then
 (if n < 218504 then
 (if n < 216222 then
 (if n < 212303 then
 175 else
 176) else
 (if n < 216829 then
 177 else
 178)) else
 (if n < 219105 then
 (if n < 219003 then
 179 else
 180) else
 (if n < 219225 then
 181 else
 182))) else
 (if n < 223106 then
 (if n < 222001 then
 (if n < 219801 then
 183 else
 184) else
 (if n < 222415 then
 185 else
 186)) else
 (if n < 225303 then
 (if n < 223551 then
 187 else
 188) else
 (if n < 228443 then
 189 else
 (if n < 231618 then
 190 else
 191))))) else
 (if n < 243321 then
 (if n < 235108 then
 (if n < 234607 then
 (if n < 234404 then
 192 else
 193) else
 (if n < 235100 then
 194 else
 195)) else
 (if n < 237700 then
 (if n < 235316 then
 196 else
 197) else
 (if n < 240912 then
 198 else
 (if n < 242008 then
 199 else
 200)))) else
 (if n < 246701 then
 (if n < 246520 then
 (if n < 246038 then
 201 else
 202) else
 (if n < 246637 then
 203 else
 204)) else
 (if n < 247309 then
 (if n < 247214 then
 205 else
 206) else
 (if n < 247400 then
 207 else
 (if n < 249105 then
 208 else
 209))))))) else
 (if n < 285215 then
 (if n < 269616 then
 (if n < 256803 then
 (if n < 253107 then
 (if n < 250200 then
 (if n < 250004 then
 210 else
 211) else
 (if n < 252522 then
 212 else
 213)) else
 (if n < 253608 then
 (if n < 253215 then
 214 else
 215) else
 (if n < 254629 then
 216 else
 217))) else
 (if n < 266239 then
 (if n < 265404 then
 (if n < 260415 then
 218 else
 219) else
 (if n < 265608 then
 220 else
 221)) else
 (if n < 268025 then
 (if n < 266700 then
 222 else
 223) else
 (if n < 268205 then
 224 else
 (if n < 268503 then
 225 else
 226))))) else
 (if n < 280316 then
 (if n < 273821 then
 (if n < 271900 then
 (if n < 270900 then
 227 else
 228) else
 (if n < 272129 then
 229 else
 230)) else
 (if n < 276511 then
 (if n < 274424 then
 231 else
 232) else
 (if n < 278900 then
 233 else
 (if n < 279204 then
 234 else
 235)))) else
 (if n < 282302 then
 (if n < 281521 then
 (if n < 280712 then
 236 else
 237) else
 (if n < 281838 then
 238 else
 239)) else
 (if n < 282712 then
 (if n < 282314 then
 240 else
 241) else
 (if n < 282809 then
 242 else
 (if n < 284510 then
 243 else
 244)))))) else
 (if n < 300852 then
 (if n < 292739 then
 (if n < 288000 then
 (if n < 285533 then
 (if n < 285407 then
 245 else
 246) else
 (if n < 287404 then
 247 else
 248)) else
 (if n < 289151 then
 (if n < 288515 then
 249 else
 250) else
 (if n < 292316 then
 251 else
 252))) else
 (if n < 294734 then
 (if n < 293225 then
 (if n < 292813 then
 253 else
 254) else
 (if n < 294618 then
 255 else
 256)) else
 (if n < 296904 then
 (if n < 295133 then
 257 else
 258) else
 (if n < 297108 then
 259 else
 (if n < 298002 then
 260 else
 261))))) else
 (if n < 314033 then
 (if n < 309828 then
 (if n < 308700 then
 (if n < 305030 then
 262 else
 263) else
 (if n < 308701 then
 264 else
 265)) else
 (if n < 312324 then
 (if n < 311138 then
 266 else
 267) else
 (if n < 313117 then
 268 else
 (if n < 313518 then
 269 else
 270)))) else
 (if n < 316510 then
 (if n < 315043 then
 (if n < 314302 then
 271 else
 272) else
 (if n < 316142 then
 273 else
 274)) else
 (if n < 317922 then
 (if n < 317503 then
 275 else
 276) else
 (if n < 319702 then
 277 else
 (if n < 322700 then
 278 else
 279))))))))) else
 (if n < 466342 then
 (if n < 391104 then
 (if n < 351634 then
 (if n < 335733 then
 (if n < 328121 then
 (if n < 326229 then
 (if n < 323200 then
 (if n < 322901 then
 280 else
 281) else
 (if n < 325622 then
 282 else
 283)) else
 (if n < 326902 then
 (if n < 326803 then
 284 else
 285) else
 (if n < 327639 then
 286 else
 287))) else
 (if n < 332417 then
 (if n < 330230 then
 (if n < 329016 then
 288 else
 289) else
 (if n < 330520 then
 290 else
 291)) else
 (if n < 333512 then
 (if n < 332500 then
 292 else
 293) else
 (if n < 333538 then
 294 else
 (if n < 333734 then
 295 else
 296))))) else
 (if n < 345843 then
 (if n < 342113 then
 (if n < 338717 then
 (if n < 336116 then
 297 else
 298) else
 (if n < 339005 then
 299 else
 300)) else
 (if n < 342809 then
 (if n < 342614 then
 301 else
 302) else
 (if n < 343107 then
 303 else
 (if n < 344121 then
 304 else
 305)))) else
 (if n < 347822 then
 (if n < 346715 then
 (if n < 346337 then
 306 else
 307) else
 (if n < 346838 then
 308 else
 309)) else
 (if n < 348628 then
 (if n < 348000 then
 310 else
 311) else
 (if n < 349121 then
 312 else
 (if n < 349411 then
 313 else
 314)))))) else
 (if n < 374028 then
 (if n < 360706 then
 (if n < 355430 then
 (if n < 354401 then
 (if n < 354339 then
 315 else
 316) else
 (if n < 354616 then
 317 else
 318)) else
 (if n < 355852 then
 (if n < 355842 then
 319 else
 320) else
 (if n < 359110 then
 321 else
 322))) else
 (if n < 366943 then
 (if n < 366221 then
 (if n < 362648 then
 323 else
 324) else
 (if n < 366800 then
 325 else
 326)) else
 (if n < 370128 then
 (if n < 368224 then
 327 else
 328) else
 (if n < 372521 then
 329 else
 (if n < 373500 then
 330 else
 331))))) else
 (if n < 381625 then
 (if n < 378730 then
 (if n < 376414 then
 (if n < 375416 then
 332 else
 333) else
 (if n < 378234 then
 334 else
 335)) else
 (if n < 381002 then
 (if n < 380909 then
 336 else
 337) else
 (if n < 381330 then
 338 else
 (if n < 381405 then
 339 else
 340)))) else
 (if n < 385225 then
 (if n < 381917 then
 (if n < 381633 then
 341 else
 342) else
 (if n < 384037 then
 343 else
 344)) else
 (if n < 386906 then
 (if n < 386320 then
 345 else
 346) else
 (if n < 389048 then
 347 else
 (if n < 389134 then
 348 else
 349))))))) else
 (if n < 427025 then
 (if n < 411130 then
 (if n < 404700 then
 (if n < 398500 then
 (if n < 393206 then
 (if n < 392728 then
 350 else
 351) else
 (if n < 397225 then
 352 else
 353)) else
 (if n < 401718 then
 (if n < 401107 then
 354 else
 355) else
 (if n < 402848 then
 356 else
 357))) else
 (if n < 406902 then
 (if n < 405830 then
 (if n < 404708 then
 358 else
 359) else
 (if n < 406605 then
 360 else
 361)) else
 (if n < 408017 then
 (if n < 407952 then
 362 else
 363) else
 (if n < 410015 then
 364 else
 (if n < 410820 then
 365 else
 366))))) else
 (if n < 418000 then
 (if n < 415422 then
 (if n < 413215 then
 (if n < 411501 then
 367 else
 368) else
 (if n < 414800 then
 369 else
 370)) else
 (if n < 416416 then
 (if n < 415443 then
 371 else
 372) else
 (if n < 416505 then
 373 else
 (if n < 417302 then
 374 else
 375)))) else
 (if n < 424224 then
 (if n < 419551 then
 (if n < 418814 then
 376 else
 377) else
 (if n < 423609 then
 378 else
 379)) else
 (if n < 424706 then
 (if n < 424605 then
 380 else
 381) else
 (if n < 424730 then
 382 else
 (if n < 426917 then
 383 else
 384)))))) else
 (if n < 447300 then
 (if n < 440337 then
 (if n < 431004 then
 (if n < 427710 then
 (if n < 427708 then
 385 else
 386) else
 (if n < 430000 then
 387 else
 388)) else
 (if n < 435711 then
 (if n < 432720 then
 389 else
 390) else
 (if n < 436021 then
 391 else
 392))) else
 (if n < 443724 then
 (if n < 443452 then
 (if n < 441521 then
 393 else
 394) else
 (if n < 443601 then
 395 else
 396)) else
 (if n < 445917 then
 (if n < 444904 then
 397 else
 398) else
 (if n < 446515 then
 399 else
 (if n < 446651 then
 400 else
 401))))) else
 (if n < 455837 then
 (if n < 452737 then
 (if n < 452451 then
 (if n < 447820 then
 402 else
 403) else
 (if n < 452500 then
 404 else
 405)) else
 (if n < 454434 then
 (if n < 453201 then
 406 else
 407) else
 (if n < 454609 then
 408 else
 (if n < 454830 then
 409 else
 410)))) else
 (if n < 462424 then
 (if n < 459208 then
 (if n < 457352 then
 411 else
 412) else
 (if n < 459910 then
 413 else
 414)) else
 (if n < 463822 then
 (if n < 463000 then
 415 else
 416) else
 (if n < 465514 then
 417 else
 (if n < 465937 then
 418 else
 419)))))))) else
 (if n < 532143 then
 (if n < 501006 then
 (if n < 480821 then
 (if n < 474800 then
 (if n < 470914 then
 (if n < 470237 then
 (if n < 468820 then
 420 else
 421) else
 (if n < 470913 then
 422 else
 423)) else
 (if n < 474110 then
 (if n < 473004 then
 424 else
 425) else
 (if n < 474700 then
 426 else
 427))) else
 (if n < 476422 then
 (if n < 475307 then
 (if n < 475024 then
 428 else
 429) else
 (if n < 476215 then
 430 else
 431)) else
 (if n < 478114 then
 (if n < 477800 then
 432 else
 433) else
 (if n < 478408 then
 434 else
 (if n < 478833 then
 435 else
 436))))) else
 (if n < 491400 then
 (if n < 484348 then
 (if n < 482400 then
 (if n < 482348 then
 437 else
 438) else
 (if n < 483951 then
 439 else
 440)) else
 (if n < 489342 then
 (if n < 487900 then
 441 else
 442) else
 (if n < 489422 then
 443 else
 (if n < 489918 then
 444 else
 445)))) else
 (if n < 496151 then
 (if n < 495000 then
 (if n < 494043 then
 446 else
 447) else
 (if n < 496112 then
 448 else
 449)) else
 (if n < 498406 then
 (if n < 497437 then
 450 else
 451) else
 (if n < 500424 then
 452 else
 (if n < 500601 then
 453 else
 454)))))) else
 (if n < 516600 then
 (if n < 509652 then
 (if n < 506451 then
 (if n < 504522 then
 (if n < 504520 then
 455 else
 456) else
 (if n < 505610 then
 457 else
 458)) else
 (if n < 507416 then
 (if n < 506629 then
 459 else
 460) else
 (if n < 507715 then
 461 else
 462))) else
 (if n < 513705 then
 (if n < 511309 then
 (if n < 509900 then
 463 else
 464) else
 (if n < 511851 then
 465 else
 466)) else
 (if n < 513848 then
 (if n < 513800 then
 467 else
 468) else
 (if n < 514621 then
 469 else
 (if n < 515413 then
 470 else
 471))))) else
 (if n < 524411 then
 (if n < 521837 then
 (if n < 518400 then
 (if n < 518148 then
 472 else
 473) else
 (if n < 519229 then
 474 else
 475)) else
 (if n < 522252 then
 (if n < 522211 then
 476 else
 477) else
 (if n < 522637 then
 478 else
 (if n < 523805 then
 479 else
 480)))) else
 (if n < 526412 then
 (if n < 525529 then
 (if n < 524838 then
 481 else
 482) else
 (if n < 526000 then
 483 else
 484)) else
 (if n < 528937 then
 (if n < 528821 then
 485 else
 486) else
 (if n < 529528 then
 487 else
 (if n < 530809 then
 488 else
 489))))))) else
 (if n < 570329 then
 (if n < 549602 then
 (if n < 542542 then
 (if n < 538342 then
 (if n < 533442 then
 (if n < 532214 then
 490 else
 491) else
 (if n < 534018 then
 492 else
 493)) else
 (if n < 539730 then
 (if n < 538616 then
 494 else
 495) else
 (if n < 541624 then
 496 else
 497))) else
 (if n < 545348 then
 (if n < 543800 then
 (if n < 543351 then
 498 else
 499) else
 (if n < 544937 then
 500 else
 501)) else
 (if n < 546730 then
 (if n < 546400 then
 502 else
 503) else
 (if n < 547720 then
 504 else
 (if n < 549111 then
 505 else
 506))))) else
 (if n < 558114 then
 (if n < 554634 then
 (if n < 553100 then
 (if n < 552851 then
 507 else
 508) else
 (if n < 554134 then
 509 else
 510)) else
 (if n < 556342 then
 (if n < 555939 then
 511 else
 512) else
 (if n < 556925 then
 513 else
 (if n < 557452 then
 514 else
 515)))) else
 (if n < 564333 then
 (if n < 562710 then
 (if n < 560300 then
 516 else
 517) else
 (if n < 563604 then
 518 else
 519)) else
 (if n < 567729 then
 (if n < 567400 then
 520 else
 521) else
 (if n < 568514 then
 522 else
 (if n < 568608 then
 523 else
 524)))))) else
 (if n < 586734 then
 (if n < 578818 then
 (if n < 572613 then
 (if n < 571906 then
 (if n < 570512 then
 525 else
 526) else
 (if n < 572517 then
 527 else
 528)) else
 (if n < 578413 then
 (if n < 574843 then
 529 else
 530) else
 (if n < 578500 then
 531 else
 532))) else
 (if n < 583138 then
 (if n < 580600 then
 (if n < 578939 then
 533 else
 534) else
 (if n < 583112 then
 535 else
 536)) else
 (if n < 584702 then
 (if n < 584600 then
 537 else
 538) else
 (if n < 586607 then
 539 else
 (if n < 586720 then
 540 else
 541))))) else
 (if n < 595108 then
 (if n < 589400 then
 (if n < 587106 then
 (if n < 586901 then
 542 else
 543) else
 (if n < 588951 then
 544 else
 545)) else
 (if n < 592238 then
 (if n < 589615 then
 546 else
 547) else
 (if n < 593512 then
 548 else
 (if n < 594810 then
 549 else
 550)))) else
 (if n < 602215 then
 (if n < 600013 then
 (if n < 599225 then
 551 else
 552) else
 (if n < 601248 then
 553 else
 554)) else
 (if n < 602933 then
 (if n < 602420 then
 555 else
 556) else
 (if n < 603403 then
 557 else
 (if n < 604410 then
 558 else
 559))))))))))

end Sporadic.LeechRelated.J2.PowerFusionCertificate.OneCentralizerCertificates
