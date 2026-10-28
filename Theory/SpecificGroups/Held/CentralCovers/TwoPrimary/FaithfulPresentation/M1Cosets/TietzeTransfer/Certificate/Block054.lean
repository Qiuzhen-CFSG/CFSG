module

public meta import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.WordLiteral
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Certificate.Block053

/-!
# Checked Tietze equalities, indices 31043 through 31123

The bounded blocks extend the already certified prefix.

Source: John Bray, ATLAS `HeG1-P1.M`; see the parent `source/README.md`.
The producer is untrusted; kernel checks supply every word equality.
-/

public section

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Certificate.Block054
open Replay

open Data

variable {G : Type*} [Group G] {g : Nat → G}

private noncomputable def steps0 : List Expr :=
  [(.eqrel (held_word% "581") (held_word% "-755,522,906,-119,422,1450,-12,533,161,-514,-2,-1772") (.denorm (held_word% "581,1772,2,514,-161,-533,12,-1450,-422,119,-906,-522,755") true 11 (.fact 19204 false))),
   (.eqrel (held_word% "1434") (held_word% "-591") (.fact 403 false)),
   (.eqrel (held_word% "2011") (held_word% "-1035") (.denorm (held_word% "2011,1035") true 1 (.fact 4318 false))),
   (.eqrel (held_word% "2019") (held_word% "-1374") (.denorm (held_word% "2019,1374") true 1 (.fact 4456 false))),
   (.eqrel (held_word% "1996") (held_word% "-1908") (.denorm (held_word% "1996,1908") true 1 (.fact 4583 false))),
   (.eqrel (held_word% "1870") (held_word% "755,122") (.denorm (held_word% "1870,-122,-755") true 2 (.denorm (held_word% "-1870,755,122") true 1 (.norm (.append (.fact 7811 false) (.norm (.append (.fact 5652 false) (.variant (.norm (.trans (.symm (.congr [(.fact 5050 false), (.same (held_word% "-765")), (.fact 4962 false), (.same (held_word% "-558")), (.same (held_word% "-1870")), (.fact 4017 false), (.fact 4454 false), (.fact 5644 false), (.fact 3798 false), (.fact 5054 false)])) (.norm (.fact 3173 false) true 3)) true 6) false 4)) false 0)) false 1)))),
   (.eqrel (held_word% "1164") (held_word% "-992,-1321") (.denorm (held_word% "1164,1321,992") true 1 (.fact 3805 false))),
   (.eqrel (held_word% "356") (held_word% "-1,172,-12,-1785") (.denorm (held_word% "356,1785,12,-172,1") true 3 (.trans (.congr [(.same (held_word% "-1785")), (.fact 5274 false), (.fact 4671 false), (.same (held_word% "172")), (.same (held_word% "-12"))]) (.norm (.trans (.symm (.congr [(.fact 4671 false), (.same (held_word% "172")), (.same (held_word% "-282")), (.same (held_word% "-434")), (.same (held_word% "434")), (.same (held_word% "282")), (.same (held_word% "-12")), (.same (held_word% "-1785")), (.same (held_word% "356"))])) (.append (.fact 9668 false) (.fact 10749 false))) false 3)))),
   (.eqrel (held_word% "120") (held_word% "-1030,291,-736,-376") (.denorm (held_word% "120,376,736,-291,1030") true 0 (.norm (.subst 425 (.fact 8927 false) (.fact 11868 false)) false 3))),
   (.eqrel (held_word% "606") (held_word% "-459,189,1772,701,-526") (.denorm (held_word% "606,526,-701,-1772,-189,459") false 3 (.norm (.append (.variant (.variant (.fact 8583 false) false 3) true 0) (.variant (.norm (.fact 8944 false) false 1) false 4)) false 2))),
   (.eqrel (held_word% "1005") (held_word% "1030,-379,-863,36") (.denorm (held_word% "1005,-36,863,379,-1030") false 4 (.norm (.subst 173 (.norm (.append (.variant (.fact 7056 false) true 0) (.norm (.fact 7523 false) false 3)) false 2) (.fact 11917 false)) true 3))),
   (.eqrel (held_word% "878") (held_word% "-741,216,-1166,-741") (.denorm (held_word% "878,741,1166,-216,741") true 2 (.trans (.congr [(.same (held_word% "-1166")), (.fact 4755 false), (.fact 4754 false), (.fact 4755 false), (.same (held_word% "216"))]) (.fact 12710 false)))),
   (.eqrel (held_word% "1837") (held_word% "1765,-799,1408,180,992") (.denorm (held_word% "1837,-992,-180,-1408,799,-1765") true 5 (.norm (.append (.variant (.variant (.fact 11013 false) true 2) true 0) (.variant (.subst 1745 (.subst 880 (.norm (.append (.fact 8052 false) (.variant (.fact 7799 false) false 2)) false 3) (.fact 11008 false)) (.fact 12924 false)) false 4)) false 2))),
   (.eqrel (held_word% "622") (held_word% "42,-928,-1208,-1,-197") (.denorm (held_word% "622,197,1,1208,928,-42") true 2 (.trans (.congr [(.same (held_word% "-1208")), (.fact 4671 false), (.same (held_word% "-197")), (.same (held_word% "-622")), (.same (held_word% "42")), (.same (held_word% "-928"))]) (.norm (.fact 14684 false) false 1)))),
   (.eqrel (held_word% "1184") (held_word% "480,-738,675,-1662,-1451") (.denorm (held_word% "1184,1451,1662,-675,738,-480") true 3 (.trans (.congr [(.same (held_word% "-1662")), (.fact 4877 false), (.same (held_word% "-1184")), (.same (held_word% "480")), (.same (held_word% "-738")), (.same (held_word% "675"))]) (.fact 12960 false)))),
   (.eqrel (held_word% "1076") (held_word% "-1662,-1451,1115,-107,1030") (.denorm (held_word% "1076,-1030,107,-1115,1451,1662") true 0 (.trans (.congr [(.same (held_word% "-1662")), (.fact 4877 false), (.same (held_word% "1115")), (.same (held_word% "-107")), (.same (held_word% "1030")), (.fact 4659 false)]) (.trans (.symm (.congr [(.same (held_word% "-1662")), (.same (held_word% "1451")), (.same (held_word% "1115")), (.same (held_word% "-107")), (.same (held_word% "1030")), (.fact 4659 false)])) (.subst 1402 (.trans (.congr [(.same (held_word% "-1662")), (.fact 5669 false), (.same (held_word% "1030")), (.fact 4659 false)]) (.fact 7857 false)) (.fact 11105 false)))))),
   (.eqrel (held_word% "601") (held_word% "-581,-755,863,764,449,250,-1083,-890") (.denorm (held_word% "601,890,1083,-250,-449,-764,-863,755,581") true 6 (.trans (.congr [(.same (held_word% "-1083")), (.same (held_word% "-890")), (.fact 5503 false), (.same (held_word% "-581")), (.same (held_word% "-755")), (.same (held_word% "863")), (.same (held_word% "764")), (.same (held_word% "449")), (.same (held_word% "250"))]) (.norm (.fact 14234 false) false 7)))),
   (.eqrel (held_word% "2045") (held_word% "-349") (.denorm (held_word% "2045,349") true 1 (.fact 3850 false))),
   (.eqrel (held_word% "1793") (held_word% "-860") (.denorm (held_word% "1793,860") true 1 (.fact 4222 false))),
   (.eqrel (held_word% "2047") (held_word% "-1114") (.denorm (held_word% "2047,1114") true 1 (.fact 4353 false))),
   (.eqrel (held_word% "1830") (held_word% "-1506") (.denorm (held_word% "1830,1506") true 1 (.fact 4497 false))),
   (.eqrel (held_word% "1818") (held_word% "-1801") (.fact 5844 false)),
   (.eqrel (held_word% "793") (held_word% "11,-933") (.denorm (held_word% "793,933,-11") true 1 (.trans (.congr [(.same (held_word% "-933")), (.fact 5647 false), (.same (held_word% "11"))]) (.norm (.append (.fact 8269 false) (.fact 5649 false)) false 2)))),
   (.eqrel (held_word% "386") (held_word% "1311,-841,-387") (.fact 10689 false)),
   (.eqrel (held_word% "536") (held_word% "-835,-246,-1233") (.denorm (held_word% "536,1233,246,835") true 2 (.fact 3532 false))),
   (.eqrel (held_word% "1125") (held_word% "-1506,-510,-313") (.variant (.fact 7192 false) true 0)),
   (.eqrel (held_word% "89") (held_word% "8,-1824") (.fact 8868 false)),
   (.eqrel (held_word% "229") (held_word% "59,-258,-59") (.denorm (held_word% "229,59,258,-59") true 1 (.fact 7107 false))),
   (.eqrel (held_word% "230") (held_word% "345,956,-558") (.denorm (held_word% "230,558,-956,-345") false 2 (.fact 8705 false))),
   (.eqrel (held_word% "2006") (held_word% "-801,398,1203,-841,-182") (.denorm (held_word% "2006,182,841,-1203,-398,801") true 5 (.norm (.trans (.symm (.congr [(.same (held_word% "1203")), (.same (held_word% "-841")), (.fact 4671 false), (.same (held_word% "629")), (.same (held_word% "933")), (.same (held_word% "-933")), (.same (held_word% "-629")), (.fact 4671 true), (.same (held_word% "-182")), (.same (held_word% "-2006")), (.same (held_word% "-801")), (.same (held_word% "398"))])) (.append (.fact 7242 false) (.variant (.norm (.fact 14345 false) false 4) false 3))) false 3))),
   (.eqrel (held_word% "650") (held_word% "745,1083,-764,1076") (.denorm (held_word% "650,-1076,764,-1083,-745") false 3 (.fact 12638 false))),
   (.eqrel (held_word% "179") (held_word% "352,189,1772,701,-634,1087") (.denorm (held_word% "179,-1087,634,-701,-1772,-189,-352") false 4 (.norm (.subst 1801 (.denorm (held_word% "-1801,-179,352,189,1772,701") true 1 (.norm (.trans (.symm (.congr [(.same (held_word% "-701")), (.same (held_word% "-1772")), (.same (held_word% "-97")), (.same (held_word% "1052")), (.fact 4760 false), (.fact 4760 true), (.same (held_word% "-1052")), (.same (held_word% "97")), (.same (held_word% "-189")), (.same (held_word% "-352")), (.same (held_word% "179")), (.same (held_word% "1801"))])) (.fact 14657 false)) false 1)) (.fact 14709 false)) true 1))),
   (.eqrel (held_word% "1809") (held_word% "867,-863,161,831,352,-1765") (.denorm (held_word% "1809,1765,-352,-831,-161,863,-867") true 6 (.norm (.trans (.symm (.congr [(.same (held_word% "-863")), (.same (held_word% "-533")), (.same (held_word% "12")), (.fact 5575 false), (.same (held_word% "422")), (.same (held_word% "-1112")), (.same (held_word% "1112")), (.same (held_word% "-422")), (.fact 5575 true), (.same (held_word% "-12")), (.same (held_word% "533")), (.same (held_word% "161")), (.same (held_word% "831")), (.same (held_word% "352")), (.same (held_word% "-1765")), (.same (held_word% "-1809")), (.same (held_word% "867"))])) (.fact 14002 false)) false 5))),
   (.eqrel (held_word% "192") (held_word% "1076,1210,-189,-574,148,-1235,459") (.denorm (held_word% "192,-459,1235,-148,574,189,-1210,-1076") true 5 (.norm (.trans (.symm (.congr [(.same (held_word% "1235")), (.same (held_word% "-148")), (.same (held_word% "149")), (.fact 4671 false), (.fact 4671 true), (.same (held_word% "-149")), (.same (held_word% "574")), (.same (held_word% "189")), (.same (held_word% "-1210")), (.fact 4659 true), (.same (held_word% "192")), (.same (held_word% "-459"))])) (.append (.fact 10731 false) (.variant (.fact 11961 false) false 4))) true 7))),
   (.eqrel (held_word% "1345") (held_word% "-322,-1106,-558,345,-1057,1321,-1703") (.denorm (held_word% "1345,1703,-1321,1057,-345,558,1106,322") true 6 (.norm (.subst 129 (.norm (.trans (.symm (.congr [(.same (held_word% "-1401")), (.same (held_word% "1057")), (.same (held_word% "-345")), (.same (held_word% "-1190")), (.same (held_word% "521")), (.same (held_word% "2018")), (.same (held_word% "863")), (.fact 4761 false), (.same (held_word% "-748")), (.same (held_word% "1087")), (.same (held_word% "-1087")), (.same (held_word% "748")), (.fact 4761 true), (.same (held_word% "-863")), (.same (held_word% "-2018")), (.same (held_word% "-521")), (.same (held_word% "1190")), (.same (held_word% "558")), (.same (held_word% "1106")), (.same (held_word% "322")), (.same (held_word% "1345")), (.same (held_word% "129"))])) (.fact 15935 false)) false 0) (.fact 15960 false)) true 2))),
   (.eqrel (held_word% "1026") (held_word% "863,-360,-688,736,352,1824,-550") (.denorm (held_word% "1026,550,-1824,-352,-736,688,360,-863") false 2 (.norm (.append (.variant (.variant (.norm (.trans (.symm (.congr [(.same (held_word% "-56")), (.same (held_word% "-1864")), (.same (held_word% "-431")), (.same (held_word% "-736")), (.fact 4760 false), (.same (held_word% "602")), (.same (held_word% "-602")), (.fact 4760 true), (.same (held_word% "736")), (.same (held_word% "-855")), (.same (held_word% "-764")), (.same (held_word% "-360")), (.same (held_word% "-688")), (.same (held_word% "736")), (.same (held_word% "180")), (.same (held_word% "-1703"))])) (.append (.fact 13454 false) (.fact 14499 false))) false 1) false 7) true 0) (.variant (.fact 14498 false) false 9)) false 6))),
   (.eqrel (held_word% "1948") (held_word% "-482") (.denorm (held_word% "1948,482") true 1 (.fact 3955 false))),
   (.eqrel (held_word% "2001") (held_word% "-1047") (.denorm (held_word% "2001,1047") true 1 (.fact 4324 false))),
   (.eqrel (held_word% "1819") (held_word% "-1809") (.denorm (held_word% "1819,1809") true 1 (.fact 4565 false))),
   (.eqrel (held_word% "78") (held_word% "442,-1675,-1047") (.denorm (held_word% "78,1047,1675,-442") true 1 (.fact 10012 false))),
   (.eqrel (held_word% "1465") (held_word% "-893,-1848,-928") (.denorm (held_word% "1465,928,1848,893") true 1 (.fact 3509 false))),
   (.eqrel (held_word% "1236") (held_word% "-1286,-56,-1507") (.denorm (held_word% "1236,1507,56,1286") true 2 (.trans (.congr [(.fact 4920 false), (.fact 5097 false), (.same (held_word% "-1286")), (.same (held_word% "-56"))]) (.denorm (held_word% "1507,1236,-1286,-56") false 2 (.norm (.append (.fact 10000 false) (.variant (.norm (.trans (.symm (.congr [(.fact 4920 false), (.fact 5097 false), (.same (held_word% "-1286")), (.same (held_word% "-843")), (.same (held_word% "803"))])) (.subst 1237 (.denorm (held_word% "-1507,-1236,1237,803") true 1 (.fact 6597 false)) (.fact 10139 false))) false 2) false 1)) false 3))))),
   (.eqrel (held_word% "1307") (held_word% "804,-1594,-804") (.denorm (held_word% "1307,804,1594,-804") true 1 (.fact 7346 false))),
   (.eqrel (held_word% "1459") (held_word% "-376,-192,-36") (.denorm (held_word% "1459,36,192,376") true 3 (.norm (.fact 136 false) true 0))),
   (.eqrel (held_word% "672") (held_word% "-475,-575,-1925,-475,-1925") (.denorm (held_word% "672,1925,475,1925,575,475") true 4 (.trans (.congr [(.same (held_word% "-1925")), (.fact 5349 false), (.same (held_word% "-475")), (.fact 5045 false), (.same (held_word% "-1925")), (.same (held_word% "-475"))]) (.denorm (held_word% "-1925,672,-475,575,-1925,-475") false 4 (.fact 11668 false))))),
   (.eqrel (held_word% "757") (held_word% "379,-1704,-379") (.fact 9184 false)),
   (.eqrel (held_word% "1013") (held_word% "-345,1208,602,-1345") (.fact 8253 false)),
   (.eqrel (held_word% "539") (held_word% "-1420,1930,-804") (.fact 12173 false)),
   (.eqrel (held_word% "614") (held_word% "-1076,-1026,36") (.denorm (held_word% "614,-36,1026,1076") true 0 (.trans (.congr [(.fact 4659 false), (.same (held_word% "-1026")), (.same (held_word% "36")), (.fact 5472 false)]) (.fact 8138 false)))),
   (.eqrel (held_word% "790") (held_word% "841,-231,-1378,-416") (.denorm (held_word% "790,416,1378,231,-841") true 2 (.trans (.congr [(.same (held_word% "-1378")), (.same (held_word% "-416")), (.fact 5482 false), (.same (held_word% "841")), (.same (held_word% "-231"))]) (.norm (.append (.fact 9118 false) (.variant (.norm (.fact 12485 false) false 2) false 3)) false 2)))),
   (.eqrel (held_word% "160") (held_word% "1621,-1675,354,-1367") (.denorm (held_word% "160,1367,-354,1675,-1621") true 1 (.trans (.congr [(.same (held_word% "-1675")), (.same (held_word% "354")), (.same (held_word% "-1367")), (.fact 5439 false), (.same (held_word% "1621"))]) (.norm (.fact 9682 false) false 4)))),
   (.eqrel (held_word% "126") (held_word% "125,319,-893,-1675") (.denorm (held_word% "126,1675,893,-319,-125") true 3 (.fact 11851 false))),
   (.eqrel (held_word% "1334") (held_word% "-107,-1,-1394,-1772,-1848,-42") (.denorm (held_word% "1334,42,1848,1772,1394,1,107") true 4 (.trans (.congr [(.same (held_word% "-1848")), (.same (held_word% "-42")), (.same (held_word% "-1334")), (.same (held_word% "-107")), (.fact 4671 false), (.same (held_word% "-1394")), (.same (held_word% "-1772"))]) (.norm (.fact 12962 false) false 3)))),
   (.eqrel (held_word% "1729") (held_word% "1848,19,743,416,1649") (.denorm (held_word% "1729,-1649,-416,-743,-19,-1848") false 5 (.norm (.append (.variant (.variant (.fact 10687 false) true 5) true 0) (.variant (.norm (.append (.fact 9356 false) (.variant (.norm (.fact 8073 false) false 4) false 6)) false 2) false 4)) false 2))),
   (.eqrel (held_word% "1964") (held_word% "1096,-799,1208,581,216") (.denorm (held_word% "1964,-216,-581,-1208,799,-1096") true 5 (.norm (.trans (.symm (.congr [(.same (held_word% "1096")), (.same (held_word% "-799")), (.same (held_word% "-130")), (.fact 4671 false), (.fact 4671 true), (.same (held_word% "130")), (.same (held_word% "1208")), (.same (held_word% "581")), (.same (held_word% "216")), (.same (held_word% "-1964"))])) (.append (.fact 9116 false) (.variant (.norm (.fact 11289 false) false 5) false 1))) false 5))),
   (.eqrel (held_word% "1335") (held_word% "-107,-1,312,-189,-1190,1675,893") (.denorm (held_word% "1335,-893,-1675,1190,189,-312,1,107") false 2 (.subst 305 (.norm (.subst 306 (.norm (.append (.fact 8661 false) (.variant (.trans (.symm (.congr [(.same (held_word% "-2018")), (.fact 2161 false), (.same (held_word% "305")), (.same (held_word% "1335")), (.fact 2917 false), (.same (held_word% "306")), (.fact 2845 false), (.same (held_word% "1190")), (.fact 1609 false), (.fact 5147 false), (.same (held_word% "1436"))])) (.norm (.fact 2919 false) false 7)) false 5)) true 2) (.fact 11850 false)) true 1) (.fact 13853 false)))),
   (.eqrel (held_word% "1693") (held_word% "-189,-1765,-855,712,-1345,-1057") (.denorm (held_word% "1693,1057,1345,-712,855,1765,189") true 1 (.norm (.fact 14667 false) false 0))),
   (.eqrel (held_word% "786") (held_word% "1,-348,1,-861,1516,1451") (.denorm (held_word% "786,-1451,-1516,861,-1,348,-1") false 2 (.trans (.congr [(.same (held_word% "-1516")), (.same (held_word% "861")), (.fact 4671 false), (.same (held_word% "348")), (.fact 4671 false), (.same (held_word% "786")), (.fact 4877 false)]) (.fact 12552 false)))),
   (.eqrel (held_word% "573") (held_word% "148,-1235,459,-243,1294,-376,-459,-574") (.denorm (held_word% "573,574,459,376,-1294,243,-459,1235,-148") false 4 (.norm (.trans (.symm (.congr [(.same (held_word% "1235")), (.same (held_word% "-148")), (.same (held_word% "149")), (.fact 4671 false), (.fact 4671 true), (.same (held_word% "-149")), (.same (held_word% "573")), (.same (held_word% "574")), (.same (held_word% "459")), (.same (held_word% "376")), (.same (held_word% "-1294")), (.same (held_word% "243")), (.same (held_word% "-459"))])) (.append (.fact 10731 false) (.variant (.norm (.fact 13384 false) true 7) false 3))) false 6))),
   (.eqrel (held_word% "1357") (held_word% "-192,-1258,-1273,675,-1076,-1258,-243") (.denorm (held_word% "1357,243,1258,1076,-675,1273,1258,192") true 7 (.trans (.congr [(.fact 5473 false), (.same (held_word% "-192")), (.same (held_word% "-1258")), (.same (held_word% "-1273")), (.same (held_word% "675")), (.fact 4659 false), (.same (held_word% "-1258")), (.fact 4846 false)]) (.denorm (held_word% "1357,-192,-1258,-1273,675,1076,-1258,243") false 3 (.norm (.fact 15508 false) false 5))))),
   (.eqrel (held_word% "978") (held_word% "675,-1662,-109,-250,-449,-1428,1053,-1848") (.denorm (held_word% "978,1848,-1053,1428,449,250,109,1662,-675") true 7 (.fact 12850 false))),
   (.eqrel (held_word% "1555") (held_word% "-284,1,-208,3,729,-780,588,1401") (.denorm (held_word% "1555,-1401,-588,780,-729,-3,208,-1,284") true 8 (.norm (.trans (.symm (.congr [(.same (held_word% "-729")), (.fact 5575 true), (.same (held_word% "588")), (.same (held_word% "-588")), (.same (held_word% "208")), (.same (held_word% "-1")), (.same (held_word% "284")), (.same (held_word% "1555")), (.same (held_word% "-1401")), (.same (held_word% "-588")), (.same (held_word% "780"))])) (.subst 1908 (.fact 15934 false) (.fact 16165 false))) true 3))),
   (.eqrel (held_word% "1635") (held_word% "-484") (.denorm (held_word% "1635,484") true 1 (.fact 3956 false))),
   (.eqrel (held_word% "1752") (held_word% "-866") (.denorm (held_word% "1752,866") true 1 (.fact 4224 false)))]

private theorem checked0 : verify db 31043 steps0 = true := by decide +kernel

private theorem prefix0 (h : ValidBefore g db initialCount) : ValidBefore g db 31107 :=
  verify_sound (Block053.valid h) steps0 checked0

private noncomputable def steps1 : List Expr :=
  [(.eqrel (held_word% "1885") (held_word% "-1458") (.denorm (held_word% "1885,1458") true 1 (.fact 4483 false))),
   (.eqrel (held_word% "1769") (held_word% "-1764") (.denorm (held_word% "1769,1764") true 1 (.fact 4560 false))),
   (.eqrel (held_word% "1893") (held_word% "-1853") (.denorm (held_word% "1893,1853") true 1 (.fact 4573 false))),
   (.eqrel (held_word% "1914") (held_word% "1168,442,-64") (.denorm (held_word% "1914,64,-442,-1168") true 3 (.norm (.append (.fact 71 false) (.fact 10020 false)) true 3))),
   (.eqrel (held_word% "999") (held_word% "-459,1432,-1011,-1432,459") (.denorm (held_word% "999,-459,1432,1011,-1432,459") true 3 (.trans (.congr [(.same (held_word% "-1432")), (.same (held_word% "459")), (.fact 5209 false), (.same (held_word% "-459")), (.same (held_word% "1432")), (.fact 5635 false)]) (.norm (.append (.fact 8089 false) (.norm (.fact 8090 false) true 1)) false 0)))),
   (.eqrel (held_word% "91") (held_word% "1401,-1555,590") (.denorm (held_word% "91,-590,1555,-1401") true 1 (.fact 8713 false))),
   (.eqrel (held_word% "787") (held_word% "-149,-1,-866,970,148") (.denorm (held_word% "787,-148,-970,866,1,149") false 2 (.fact 9713 false))),
   (.eqrel (held_word% "1580") (held_word% "1401,1032,-51,-1032,-1401") (.denorm (held_word% "1580,1401,1032,51,-1032,-1401") false 5 (.trans (.symm (.congr [(.fact 4552 false), (.same (held_word% "-1401")), (.fact 4851 false), (.same (held_word% "1401")), (.fact 3146 false), (.same (held_word% "1032")), (.fact 1907 false), (.same (held_word% "51")), (.fact 4141 false), (.same (held_word% "-1032"))])) (.norm (.fact 200 false) true 2)))),
   (.eqrel (held_word% "915") (held_word% "869,1357,-192,-36,650") (.denorm (held_word% "915,-650,36,192,-1357,-869") false 4 (.denorm (held_word% "-1357,-869,915,-650,36,192") true 3 (.norm (.fact 12502 false) true 2)))),
   (.eqrel (held_word% "1085") (held_word% "-1032,-1208,-398,801") (.denorm (held_word% "1085,-801,398,1208,1032") true 1 (.norm (.append (.variant (.fact 7660 false) true 0) (.norm (.trans (.symm (.congr [(.same (held_word% "1757")), (.same (held_word% "738")), (.same (held_word% "801")), (.fact 5227 false), (.same (held_word% "634")), (.same (held_word% "-634")), (.fact 5227 true), (.same (held_word% "-801")), (.same (held_word% "-398")), (.same (held_word% "801")), (.same (held_word% "-1085")), (.same (held_word% "-1032")), (.same (held_word% "630"))])) (.fact 12116 false)) true 6)) true 5))),
   (.eqrel (held_word% "612") (held_word% "-371,-736,-630,-1555,-581,-1052,-8") (.denorm (held_word% "612,8,1052,581,1555,630,736,371") true 3 (.trans (.congr [(.same (held_word% "-1555")), (.same (held_word% "-581")), (.same (held_word% "-1052")), (.same (held_word% "-8")), (.same (held_word% "-612")), (.fact 7805 false), (.same (held_word% "-736")), (.same (held_word% "-630"))]) (.norm (.fact 15294 false) false 5)))),
   (.eqrel (held_word% "2040") (held_word% "-608") (.denorm (held_word% "2040,608") true 1 (.fact 4064 false))),
   (.eqrel (held_word% "1766") (held_word% "-612") (.denorm (held_word% "1766,612") true 1 (.fact 4066 false))),
   (.eqrel (held_word% "2050") (held_word% "-951") (.denorm (held_word% "2050,951") true 1 (.fact 4284 false))),
   (.eqrel (held_word% "1802") (held_word% "-973") (.denorm (held_word% "1802,973") true 1 (.fact 4298 false))),
   (.eqrel (held_word% "1584") (held_word% "-1165") (.denorm (held_word% "1584,1165") true 1 (.fact 4379 false))),
   (.eqrel (held_word% "1664") (held_word% "-1398,-947,588") (.denorm (held_word% "1664,-588,947,1398") true 3 (.fact 5729 false)))]

private theorem checked1 : verify db 31107 steps1 = true := by decide +kernel

private theorem prefix1 (h : ValidBefore g db initialCount) : ValidBefore g db 31124 :=
  verify_sound (prefix0 h) steps1 checked1

theorem valid (h : ValidBefore g db initialCount) : ValidBefore g db 31124 := prefix1 h

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Certificate.Block054
