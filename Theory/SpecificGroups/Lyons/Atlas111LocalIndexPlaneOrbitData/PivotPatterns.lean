module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.MaskedChecks

/-!
# Certified pivot masks for the complete Lyons candidate data

The 219 candidate pivot patterns were extracted from the retained 8,835,156-node
untrusted enumeration. Every pattern below has kernel-checked increasing pivots
and mask coverage. `get` uses a balanced search, returning a certified pattern
also for codes not in the extracted catalogue. This makes it total without any
external completeness assumption. Each node must still pass the masked shape
check; choosing an unsuitable pattern cannot certify an incorrect basis.

Codes contain seven little-endian seven-bit pivot indices (the field at bit
2478 in the enumeration record). Source: the exact enumeration adapted from
`Atlas111PlaneOrbitSource/GenerateOrbit.py`, with the format documented in
`Enumeration/source/README.md` in the retained producer workspace.
`PivotPatterns/source/Generate.py` reproduces these declarations from its binary
blocks. The catalogue is not a proof of any orbit cardinality or full-data check.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitData.PivotPatterns

/-- Pivot code 26561157824640. -/
def p000 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 6]
  increasing := by decide +kernel
  mask := 2097151
  covers := by decide +kernel

/-- Pivot code 30959204335744. -/
def p001 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 7]
  increasing := by decide +kernel
  mask := 14942207
  covers := by decide +kernel

/-- Pivot code 30993564074112. -/
def p002 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 7]
  increasing := by decide +kernel
  mask := 16547839
  covers := by decide +kernel

/-- Pivot code 30993832509568. -/
def p003 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 7]
  increasing := by decide +kernel
  mask := 16748543
  covers := by decide +kernel

/-- Pivot code 30993834606720. -/
def p004 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 7]
  increasing := by decide +kernel
  mask := 16773631
  covers := by decide +kernel

/-- Pivot code 30993834623104. -/
def p005 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 6, 7]
  increasing := by decide +kernel
  mask := 16776767
  covers := by decide +kernel

/-- Pivot code 30993834623232. -/
def p006 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 6, 7]
  increasing := by decide +kernel
  mask := 16777159
  covers := by decide +kernel

/-- Pivot code 30993834623233. -/
def p007 : MaskPattern where
  pivot := ![1, 2, 3, 4, 5, 6, 7]
  increasing := by decide +kernel
  mask := 16777208
  covers := by decide +kernel

/-- Pivot code 35357250846848. -/
def p008 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 8]
  increasing := by decide +kernel
  mask := 117702655
  covers := by decide +kernel

/-- Pivot code 35391610585216. -/
def p009 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 8]
  increasing := by decide +kernel
  mask := 119308287
  covers := by decide +kernel

/-- Pivot code 35391879020672. -/
def p010 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 8]
  increasing := by decide +kernel
  mask := 119508991
  covers := by decide +kernel

/-- Pivot code 35391881117824. -/
def p011 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 8]
  increasing := by decide +kernel
  mask := 119534079
  covers := by decide +kernel

/-- Pivot code 35391881134208. -/
def p012 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 6, 8]
  increasing := by decide +kernel
  mask := 119537215
  covers := by decide +kernel

/-- Pivot code 35391881134336. -/
def p013 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 6, 8]
  increasing := by decide +kernel
  mask := 119537607
  covers := by decide +kernel

/-- Pivot code 35391881134337. -/
def p014 : MaskPattern where
  pivot := ![1, 2, 3, 4, 5, 6, 8]
  increasing := by decide +kernel
  mask := 119537656
  covers := by decide +kernel

/-- Pivot code 35425970323584. -/
def p015 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 8]
  increasing := by decide +kernel
  mask := 132153343
  covers := by decide +kernel

/-- Pivot code 35426238759040. -/
def p016 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 8]
  increasing := by decide +kernel
  mask := 132354047
  covers := by decide +kernel

/-- Pivot code 35426240856192. -/
def p017 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 8]
  increasing := by decide +kernel
  mask := 132379135
  covers := by decide +kernel

/-- Pivot code 35426240872576. -/
def p018 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 7, 8]
  increasing := by decide +kernel
  mask := 132382271
  covers := by decide +kernel

/-- Pivot code 35426240872704. -/
def p019 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 7, 8]
  increasing := by decide +kernel
  mask := 132382663
  covers := by decide +kernel

/-- Pivot code 35426507194496. -/
def p020 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 7, 8]
  increasing := by decide +kernel
  mask := 133959679
  covers := by decide +kernel

/-- Pivot code 35426509291648. -/
def p021 : MaskPattern where
  pivot := ![0, 1, 2, 4, 6, 7, 8]
  increasing := by decide +kernel
  mask := 133984767
  covers := by decide +kernel

/-- Pivot code 35426509308032. -/
def p022 : MaskPattern where
  pivot := ![0, 1, 3, 4, 6, 7, 8]
  increasing := by decide +kernel
  mask := 133987903
  covers := by decide +kernel

/-- Pivot code 35426511388800. -/
def p023 : MaskPattern where
  pivot := ![0, 1, 2, 5, 6, 7, 8]
  increasing := by decide +kernel
  mask := 134185471
  covers := by decide +kernel

/-- Pivot code 35426511405184. -/
def p024 : MaskPattern where
  pivot := ![0, 1, 3, 5, 6, 7, 8]
  increasing := by decide +kernel
  mask := 134188607
  covers := by decide +kernel

/-- Pivot code 35426511421568. -/
def p025 : MaskPattern where
  pivot := ![0, 1, 4, 5, 6, 7, 8]
  increasing := by decide +kernel
  mask := 134213695
  covers := by decide +kernel

/-- Pivot code 39755297357952. -/
def p026 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 9]
  increasing := by decide +kernel
  mask := 939786239
  covers := by decide +kernel

/-- Pivot code 39789657096320. -/
def p027 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 9]
  increasing := by decide +kernel
  mask := 941391871
  covers := by decide +kernel

/-- Pivot code 39789925531776. -/
def p028 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 9]
  increasing := by decide +kernel
  mask := 941592575
  covers := by decide +kernel

/-- Pivot code 39789927628928. -/
def p029 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 9]
  increasing := by decide +kernel
  mask := 941617663
  covers := by decide +kernel

/-- Pivot code 39789927645312. -/
def p030 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 6, 9]
  increasing := by decide +kernel
  mask := 941620799
  covers := by decide +kernel

/-- Pivot code 39789927645440. -/
def p031 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 6, 9]
  increasing := by decide +kernel
  mask := 941621191
  covers := by decide +kernel

/-- Pivot code 39789927645441. -/
def p032 : MaskPattern where
  pivot := ![1, 2, 3, 4, 5, 6, 9]
  increasing := by decide +kernel
  mask := 941621240
  covers := by decide +kernel

/-- Pivot code 39824016834688. -/
def p033 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 9]
  increasing := by decide +kernel
  mask := 954236927
  covers := by decide +kernel

/-- Pivot code 39824285270144. -/
def p034 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 9]
  increasing := by decide +kernel
  mask := 954437631
  covers := by decide +kernel

/-- Pivot code 39824287367296. -/
def p035 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 9]
  increasing := by decide +kernel
  mask := 954462719
  covers := by decide +kernel

/-- Pivot code 39824287383680. -/
def p036 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 7, 9]
  increasing := by decide +kernel
  mask := 954465855
  covers := by decide +kernel

/-- Pivot code 39824553705600. -/
def p037 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 7, 9]
  increasing := by decide +kernel
  mask := 956043263
  covers := by decide +kernel

/-- Pivot code 39824555802752. -/
def p038 : MaskPattern where
  pivot := ![0, 1, 2, 4, 6, 7, 9]
  increasing := by decide +kernel
  mask := 956068351
  covers := by decide +kernel

/-- Pivot code 39824555819136. -/
def p039 : MaskPattern where
  pivot := ![0, 1, 3, 4, 6, 7, 9]
  increasing := by decide +kernel
  mask := 956071487
  covers := by decide +kernel

/-- Pivot code 39824557899904. -/
def p040 : MaskPattern where
  pivot := ![0, 1, 2, 5, 6, 7, 9]
  increasing := by decide +kernel
  mask := 956269055
  covers := by decide +kernel

/-- Pivot code 39824557932800. -/
def p041 : MaskPattern where
  pivot := ![0, 2, 4, 5, 6, 7, 9]
  increasing := by decide +kernel
  mask := 956297671
  covers := by decide +kernel

/-- Pivot code 39858376573056. -/
def p042 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 8, 9]
  increasing := by decide +kernel
  mask := 1056997375
  covers := by decide +kernel

/-- Pivot code 39858645008512. -/
def p043 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 8, 9]
  increasing := by decide +kernel
  mask := 1057198079
  covers := by decide +kernel

/-- Pivot code 39858647105664. -/
def p044 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 8, 9]
  increasing := by decide +kernel
  mask := 1057223167
  covers := by decide +kernel

/-- Pivot code 39858647122048. -/
def p045 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 8, 9]
  increasing := by decide +kernel
  mask := 1057226303
  covers := by decide +kernel

/-- Pivot code 39858647122176. -/
def p046 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 8, 9]
  increasing := by decide +kernel
  mask := 1057226695
  covers := by decide +kernel

/-- Pivot code 39858913443968. -/
def p047 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 8, 9]
  increasing := by decide +kernel
  mask := 1058803711
  covers := by decide +kernel

/-- Pivot code 39858917638272. -/
def p048 : MaskPattern where
  pivot := ![0, 1, 2, 5, 6, 8, 9]
  increasing := by decide +kernel
  mask := 1059029503
  covers := by decide +kernel

/-- Pivot code 39859181879424. -/
def p049 : MaskPattern where
  pivot := ![0, 1, 2, 3, 7, 8, 9]
  increasing := by decide +kernel
  mask := 1071648767
  covers := by decide +kernel

/-- Pivot code 39859183976576. -/
def p050 : MaskPattern where
  pivot := ![0, 1, 2, 4, 7, 8, 9]
  increasing := by decide +kernel
  mask := 1071673855
  covers := by decide +kernel

/-- Pivot code 44153343869056. -/
def p051 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 10]
  increasing := by decide +kernel
  mask := 7516454911
  covers := by decide +kernel

/-- Pivot code 44187703607424. -/
def p052 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 10]
  increasing := by decide +kernel
  mask := 7518060543
  covers := by decide +kernel

/-- Pivot code 44187972042880. -/
def p053 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 10]
  increasing := by decide +kernel
  mask := 7518261247
  covers := by decide +kernel

/-- Pivot code 44187974140032. -/
def p054 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 10]
  increasing := by decide +kernel
  mask := 7518286335
  covers := by decide +kernel

/-- Pivot code 44187974156416. -/
def p055 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 6, 10]
  increasing := by decide +kernel
  mask := 7518289471
  covers := by decide +kernel

/-- Pivot code 44187974156544. -/
def p056 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 6, 10]
  increasing := by decide +kernel
  mask := 7518289863
  covers := by decide +kernel

/-- Pivot code 44187974156545. -/
def p057 : MaskPattern where
  pivot := ![1, 2, 3, 4, 5, 6, 10]
  increasing := by decide +kernel
  mask := 7518289912
  covers := by decide +kernel

/-- Pivot code 44222063345792. -/
def p058 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 10]
  increasing := by decide +kernel
  mask := 7530905599
  covers := by decide +kernel

/-- Pivot code 44222331781248. -/
def p059 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 10]
  increasing := by decide +kernel
  mask := 7531106303
  covers := by decide +kernel

/-- Pivot code 44222333878400. -/
def p060 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 10]
  increasing := by decide +kernel
  mask := 7531131391
  covers := by decide +kernel

/-- Pivot code 44222333894784. -/
def p061 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 7, 10]
  increasing := by decide +kernel
  mask := 7531134527
  covers := by decide +kernel

/-- Pivot code 44222333894912. -/
def p062 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 7, 10]
  increasing := by decide +kernel
  mask := 7531134919
  covers := by decide +kernel

/-- Pivot code 44222333894913. -/
def p063 : MaskPattern where
  pivot := ![1, 2, 3, 4, 5, 7, 10]
  increasing := by decide +kernel
  mask := 7531134968
  covers := by decide +kernel

/-- Pivot code 44222600216704. -/
def p064 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 7, 10]
  increasing := by decide +kernel
  mask := 7532711935
  covers := by decide +kernel

/-- Pivot code 44222602313856. -/
def p065 : MaskPattern where
  pivot := ![0, 1, 2, 4, 6, 7, 10]
  increasing := by decide +kernel
  mask := 7532737023
  covers := by decide +kernel

/-- Pivot code 44256423084160. -/
def p066 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 8, 10]
  increasing := by decide +kernel
  mask := 7633666047
  covers := by decide +kernel

/-- Pivot code 44256691519616. -/
def p067 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 8, 10]
  increasing := by decide +kernel
  mask := 7633866751
  covers := by decide +kernel

/-- Pivot code 44256693616768. -/
def p068 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 8, 10]
  increasing := by decide +kernel
  mask := 7633891839
  covers := by decide +kernel

/-- Pivot code 44256693633152. -/
def p069 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 8, 10]
  increasing := by decide +kernel
  mask := 7633894975
  covers := by decide +kernel

/-- Pivot code 44256959955072. -/
def p070 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 8, 10]
  increasing := by decide +kernel
  mask := 7635472383
  covers := by decide +kernel

/-- Pivot code 44290782822528. -/
def p071 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 9, 10]
  increasing := by decide +kernel
  mask := 8455749631
  covers := by decide +kernel

/-- Pivot code 44291053355136. -/
def p072 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 9, 10]
  increasing := by decide +kernel
  mask := 8455975423
  covers := by decide +kernel

/-- Pivot code 48551390380160. -/
def p073 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 11]
  increasing := by decide +kernel
  mask := 60129804287
  covers := by decide +kernel

/-- Pivot code 48585750118528. -/
def p074 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 11]
  increasing := by decide +kernel
  mask := 60131409919
  covers := by decide +kernel

/-- Pivot code 48586018553984. -/
def p075 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 11]
  increasing := by decide +kernel
  mask := 60131610623
  covers := by decide +kernel

/-- Pivot code 48586020651136. -/
def p076 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 11]
  increasing := by decide +kernel
  mask := 60131635711
  covers := by decide +kernel

/-- Pivot code 48586020667648. -/
def p077 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 6, 11]
  increasing := by decide +kernel
  mask := 60131639239
  covers := by decide +kernel

/-- Pivot code 48620109856896. -/
def p078 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 11]
  increasing := by decide +kernel
  mask := 60144254975
  covers := by decide +kernel

/-- Pivot code 48620378292352. -/
def p079 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 11]
  increasing := by decide +kernel
  mask := 60144455679
  covers := by decide +kernel

/-- Pivot code 48620380389504. -/
def p080 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 11]
  increasing := by decide +kernel
  mask := 60144480767
  covers := by decide +kernel

/-- Pivot code 48620380405888. -/
def p081 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 7, 11]
  increasing := by decide +kernel
  mask := 60144483903
  covers := by decide +kernel

/-- Pivot code 48620646727808. -/
def p082 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 7, 11]
  increasing := by decide +kernel
  mask := 60146061311
  covers := by decide +kernel

/-- Pivot code 48654469595264. -/
def p083 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 8, 11]
  increasing := by decide +kernel
  mask := 60247015423
  covers := by decide +kernel

/-- Pivot code 48654738030720. -/
def p084 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 8, 11]
  increasing := by decide +kernel
  mask := 60247216127
  covers := by decide +kernel

/-- Pivot code 48654740144384. -/
def p085 : MaskPattern where
  pivot := ![0, 2, 3, 4, 5, 8, 11]
  increasing := by decide +kernel
  mask := 60247244743
  covers := by decide +kernel

/-- Pivot code 48688829333632. -/
def p086 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 9, 11]
  increasing := by decide +kernel
  mask := 61069099007
  covers := by decide +kernel

/-- Pivot code 48689099866240. -/
def p087 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 9, 11]
  increasing := by decide +kernel
  mask := 61069324799
  covers := by decide +kernel

/-- Pivot code 52949436891264. -/
def p088 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 12]
  increasing := by decide +kernel
  mask := 481036599295
  covers := by decide +kernel

/-- Pivot code 52983796629632. -/
def p089 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 12]
  increasing := by decide +kernel
  mask := 481038204927
  covers := by decide +kernel

/-- Pivot code 52984065065088. -/
def p090 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 12]
  increasing := by decide +kernel
  mask := 481038405631
  covers := by decide +kernel

/-- Pivot code 52984067162240. -/
def p091 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 12]
  increasing := by decide +kernel
  mask := 481038430719
  covers := by decide +kernel

/-- Pivot code 53018156368000. -/
def p092 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 12]
  increasing := by decide +kernel
  mask := 481051049983
  covers := by decide +kernel

/-- Pivot code 53018424803456. -/
def p093 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 12]
  increasing := by decide +kernel
  mask := 481051250687
  covers := by decide +kernel

/-- Pivot code 53018426900608. -/
def p094 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 12]
  increasing := by decide +kernel
  mask := 481051275775
  covers := by decide +kernel

/-- Pivot code 53052516106368. -/
def p095 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 8, 12]
  increasing := by decide +kernel
  mask := 481153810431
  covers := by decide +kernel

/-- Pivot code 57347483402368. -/
def p096 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 13]
  increasing := by decide +kernel
  mask := 3848290959359
  covers := by decide +kernel

/-- Pivot code 57381843140736. -/
def p097 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 13]
  increasing := by decide +kernel
  mask := 3848292564991
  covers := by decide +kernel

/-- Pivot code 57382111576192. -/
def p098 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 13]
  increasing := by decide +kernel
  mask := 3848292765695
  covers := by decide +kernel

/-- Pivot code 57416202879104. -/
def p099 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 13]
  increasing := by decide +kernel
  mask := 3848305410047
  covers := by decide +kernel

/-- Pivot code 57416473411712. -/
def p100 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 13]
  increasing := by decide +kernel
  mask := 3848305635839
  covers := by decide +kernel

/-- Pivot code 61745529913472. -/
def p101 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 14]
  increasing := by decide +kernel
  mask := 30786325839871
  covers := by decide +kernel

/-- Pivot code 61779889651840. -/
def p102 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 14]
  increasing := by decide +kernel
  mask := 30786327445503
  covers := by decide +kernel

/-- Pivot code 66143576424576. -/
def p103 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 15]
  increasing := by decide +kernel
  mask := 246290604883967
  covers := by decide +kernel

/-- Pivot code 66177936162944. -/
def p104 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 15]
  increasing := by decide +kernel
  mask := 246290606489599
  covers := by decide +kernel

/-- Pivot code 198084971757696. -/
def p105 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864317726719
  covers := by decide +kernel

/-- Pivot code 198119331496064. -/
def p106 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864319332351
  covers := by decide +kernel

/-- Pivot code 198119599931520. -/
def p107 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864319533055
  covers := by decide +kernel

/-- Pivot code 198119602028672. -/
def p108 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864319558143
  covers := by decide +kernel

/-- Pivot code 198119602045056. -/
def p109 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 6, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864319561279
  covers := by decide +kernel

/-- Pivot code 198153691234432. -/
def p110 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864332177407
  covers := by decide +kernel

/-- Pivot code 198153959669888. -/
def p111 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864332378111
  covers := by decide +kernel

/-- Pivot code 198153961767040. -/
def p112 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864332403199
  covers := by decide +kernel

/-- Pivot code 198153961783424. -/
def p113 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 7, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864332406335
  covers := by decide +kernel

/-- Pivot code 198154228105344. -/
def p114 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 7, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864333983743
  covers := by decide +kernel

/-- Pivot code 198188050972800. -/
def p115 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 8, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864434937855
  covers := by decide +kernel

/-- Pivot code 198188319408256. -/
def p116 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 8, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864435138559
  covers := by decide +kernel

/-- Pivot code 198188321505408. -/
def p117 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 8, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864435163647
  covers := by decide +kernel

/-- Pivot code 198188321521792. -/
def p118 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 8, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864435166783
  covers := by decide +kernel

/-- Pivot code 198188587843712. -/
def p119 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 8, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258864436744191
  covers := by decide +kernel

/-- Pivot code 198222410711168. -/
def p120 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 9, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258865257021439
  covers := by decide +kernel

/-- Pivot code 198222679146624. -/
def p121 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 9, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258865257222143
  covers := by decide +kernel

/-- Pivot code 198222681243776. -/
def p122 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 9, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258865257247231
  covers := by decide +kernel

/-- Pivot code 198222681260160. -/
def p123 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 9, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258865257250367
  covers := by decide +kernel

/-- Pivot code 198256770449536. -/
def p124 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 10, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258871833690111
  covers := by decide +kernel

/-- Pivot code 198257038884992. -/
def p125 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 10, 45]
  increasing := by decide +kernel
  mask := 304893000761160863263183648258871833890815
  covers := by decide +kernel

/-- Pivot code 202483018268800. -/
def p126 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914539978751
  covers := by decide +kernel

/-- Pivot code 202517378007168. -/
def p127 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914541584383
  covers := by decide +kernel

/-- Pivot code 202517646442624. -/
def p128 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914541785087
  covers := by decide +kernel

/-- Pivot code 202517648539776. -/
def p129 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914541810175
  covers := by decide +kernel

/-- Pivot code 202517648556160. -/
def p130 : MaskPattern where
  pivot := ![0, 1, 3, 4, 5, 6, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914541813311
  covers := by decide +kernel

/-- Pivot code 202551737745536. -/
def p131 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914554429439
  covers := by decide +kernel

/-- Pivot code 202552006180992. -/
def p132 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914554630143
  covers := by decide +kernel

/-- Pivot code 202552008278144. -/
def p133 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 7, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914554655231
  covers := by decide +kernel

/-- Pivot code 202586097483904. -/
def p134 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 8, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914657189887
  covers := by decide +kernel

/-- Pivot code 202586365919360. -/
def p135 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 8, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914657390591
  covers := by decide +kernel

/-- Pivot code 202586634354816. -/
def p136 : MaskPattern where
  pivot := ![0, 1, 2, 3, 6, 8, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070914658996223
  covers := by decide +kernel

/-- Pivot code 202620457222272. -/
def p137 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 9, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070915479273471
  covers := by decide +kernel

/-- Pivot code 202620725657728. -/
def p138 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 9, 46]
  increasing := by decide +kernel
  mask := 2439144006089286906105469186070915479474175
  covers := by decide +kernel

/-- Pivot code 206881064779904. -/
def p139 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 47]
  increasing := by decide +kernel
  mask := 19513152048714295248843753488567316317995007
  covers := by decide +kernel

/-- Pivot code 206915424518272. -/
def p140 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 47]
  increasing := by decide +kernel
  mask := 19513152048714295248843753488567316319600639
  covers := by decide +kernel

/-- Pivot code 206915692953728. -/
def p141 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 6, 47]
  increasing := by decide +kernel
  mask := 19513152048714295248843753488567316319801343
  covers := by decide +kernel

/-- Pivot code 206915695050880. -/
def p142 : MaskPattern where
  pivot := ![0, 1, 2, 4, 5, 6, 47]
  increasing := by decide +kernel
  mask := 19513152048714295248843753488567316319826431
  covers := by decide +kernel

/-- Pivot code 206949784256640. -/
def p143 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 47]
  increasing := by decide +kernel
  mask := 19513152048714295248843753488567316332445695
  covers := by decide +kernel

/-- Pivot code 206950052692096. -/
def p144 : MaskPattern where
  pivot := ![0, 1, 2, 3, 5, 7, 47]
  increasing := by decide +kernel
  mask := 19513152048714295248843753488567316332646399
  covers := by decide +kernel

/-- Pivot code 211279111291008. -/
def p145 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 48]
  increasing := by decide +kernel
  mask := 156105216389714361990750027908538530542125055
  covers := by decide +kernel

/-- Pivot code 211313471029376. -/
def p146 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 6, 48]
  increasing := by decide +kernel
  mask := 156105216389714361990750027908538530543730687
  covers := by decide +kernel

/-- Pivot code 211347830767744. -/
def p147 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 7, 48]
  increasing := by decide +kernel
  mask := 156105216389714361990750027908538530556575743
  covers := by decide +kernel

/-- Pivot code 215677157802112. -/
def p148 : MaskPattern where
  pivot := ![0, 1, 2, 3, 4, 5, 49]
  increasing := by decide +kernel
  mask := 1248841731117714895926000223268308244335165439
  covers := by decide +kernel

/-- Pivot code 257060350492800. -/
def p149 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431575551
  covers := by decide +kernel

/-- Pivot code 257060350509184. -/
def p150 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431578687
  covers := by decide +kernel

/-- Pivot code 257060350509312. -/
def p151 : MaskPattern where
  pivot := ![0, 2, 3, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431579079
  covers := by decide +kernel

/-- Pivot code 257060350509313. -/
def p152 : MaskPattern where
  pivot := ![1, 2, 3, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431579128
  covers := by decide +kernel

/-- Pivot code 257060350525568. -/
def p153 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431603775
  covers := by decide +kernel

/-- Pivot code 257060350525696. -/
def p154 : MaskPattern where
  pivot := ![0, 2, 4, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431604167
  covers := by decide +kernel

/-- Pivot code 257060350525697. -/
def p155 : MaskPattern where
  pivot := ![1, 2, 4, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431604216
  covers := by decide +kernel

/-- Pivot code 257060350525824. -/
def p156 : MaskPattern where
  pivot := ![0, 3, 4, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431607303
  covers := by decide +kernel

/-- Pivot code 257060350541952. -/
def p157 : MaskPattern where
  pivot := ![0, 1, 5, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431804479
  covers := by decide +kernel

/-- Pivot code 257060350542080. -/
def p158 : MaskPattern where
  pivot := ![0, 2, 5, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431804871
  covers := by decide +kernel

/-- Pivot code 257060350542081. -/
def p159 : MaskPattern where
  pivot := ![1, 2, 5, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431804920
  covers := by decide +kernel

/-- Pivot code 257060350542208. -/
def p160 : MaskPattern where
  pivot := ![0, 3, 5, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400431808007
  covers := by decide +kernel

/-- Pivot code 257060350558336. -/
def p161 : MaskPattern where
  pivot := ![0, 1, 6, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400433410111
  covers := by decide +kernel

/-- Pivot code 257060350558464. -/
def p162 : MaskPattern where
  pivot := ![0, 2, 6, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400433410503
  covers := by decide +kernel

/-- Pivot code 257060350558592. -/
def p163 : MaskPattern where
  pivot := ![0, 3, 6, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400433413639
  covers := by decide +kernel

/-- Pivot code 257060350574720. -/
def p164 : MaskPattern where
  pivot := ![0, 1, 7, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400446255167
  covers := by decide +kernel

/-- Pivot code 257060350591232. -/
def p165 : MaskPattern where
  pivot := ![0, 2, 8, 55, 56, 57, 58]
  increasing := by decide +kernel
  mask := 191515174555841518401410860479141726895713400549016007
  covers := by decide +kernel

/-- Pivot code 261458397003904. -/
def p166 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853395967
  covers := by decide +kernel

/-- Pivot code 261458397020288. -/
def p167 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853399103
  covers := by decide +kernel

/-- Pivot code 261458397020416. -/
def p168 : MaskPattern where
  pivot := ![0, 2, 3, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853399495
  covers := by decide +kernel

/-- Pivot code 261458397036672. -/
def p169 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853424191
  covers := by decide +kernel

/-- Pivot code 261458397036800. -/
def p170 : MaskPattern where
  pivot := ![0, 2, 4, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853424583
  covers := by decide +kernel

/-- Pivot code 261458397036801. -/
def p171 : MaskPattern where
  pivot := ![1, 2, 4, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853424632
  covers := by decide +kernel

/-- Pivot code 261458397036928. -/
def p172 : MaskPattern where
  pivot := ![0, 3, 4, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853427719
  covers := by decide +kernel

/-- Pivot code 261458397053056. -/
def p173 : MaskPattern where
  pivot := ![0, 1, 5, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540853624895
  covers := by decide +kernel

/-- Pivot code 261458397069440. -/
def p174 : MaskPattern where
  pivot := ![0, 1, 6, 55, 56, 57, 59]
  increasing := by decide +kernel
  mask := 1364832073031287675582020303141097195603810540855230527
  covers := by decide +kernel

/-- Pivot code 261492756742272. -/
def p175 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 58, 59]
  increasing := by decide +kernel
  mask := 1511496685340718445229596483473841629192322683406123519
  covers := by decide +kernel

/-- Pivot code 261492756758656. -/
def p176 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 58, 59]
  increasing := by decide +kernel
  mask := 1511496685340718445229596483473841629192322683406126655
  covers := by decide +kernel

/-- Pivot code 261492756758784. -/
def p177 : MaskPattern where
  pivot := ![0, 2, 3, 55, 56, 58, 59]
  increasing := by decide +kernel
  mask := 1511496685340718445229596483473841629192322683406127047
  covers := by decide +kernel

/-- Pivot code 261492756775040. -/
def p178 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 58, 59]
  increasing := by decide +kernel
  mask := 1511496685340718445229596483473841629192322683406151743
  covers := by decide +kernel

/-- Pivot code 261492756791424. -/
def p179 : MaskPattern where
  pivot := ![0, 1, 5, 55, 56, 58, 59]
  increasing := by decide +kernel
  mask := 1511496685340718445229596483473841629192322683406352447
  covers := by decide +kernel

/-- Pivot code 261493025177728. -/
def p180 : MaskPattern where
  pivot := ![0, 1, 2, 55, 57, 58, 59]
  increasing := by decide +kernel
  mask := 1529829761879397291435543506015434683390886701225214463
  covers := by decide +kernel

/-- Pivot code 261493025194112. -/
def p181 : MaskPattern where
  pivot := ![0, 1, 3, 55, 57, 58, 59]
  increasing := by decide +kernel
  mask := 1529829761879397291435543506015434683390886701225217599
  covers := by decide +kernel

/-- Pivot code 261493025194240. -/
def p182 : MaskPattern where
  pivot := ![0, 2, 3, 55, 57, 58, 59]
  increasing := by decide +kernel
  mask := 1529829761879397291435543506015434683390886701225217991
  covers := by decide +kernel

/-- Pivot code 261493027274880. -/
def p183 : MaskPattern where
  pivot := ![0, 1, 2, 56, 57, 58, 59]
  increasing := by decide +kernel
  mask := 1532121396446732147211286883833133815165707203452600831
  covers := by decide +kernel

/-- Pivot code 265856443515008. -/
def p184 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 60]
  increasing := by decide +kernel
  mask := 10751367260834856933026895844436740945268587664227959295
  covers := by decide +kernel

/-- Pivot code 265856443531392. -/
def p185 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 57, 60]
  increasing := by decide +kernel
  mask := 10751367260834856933026895844436740945268587664227962431
  covers := by decide +kernel

/-- Pivot code 265856443547776. -/
def p186 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 57, 60]
  increasing := by decide +kernel
  mask := 10751367260834856933026895844436740945268587664227987519
  covers := by decide +kernel

/-- Pivot code 265856443547904. -/
def p187 : MaskPattern where
  pivot := ![0, 2, 4, 55, 56, 57, 60]
  increasing := by decide +kernel
  mask := 10751367260834856933026895844436740945268587664227987911
  covers := by decide +kernel

/-- Pivot code 265856443564160. -/
def p188 : MaskPattern where
  pivot := ![0, 1, 5, 55, 56, 57, 60]
  increasing := by decide +kernel
  mask := 10751367260834856933026895844436740945268587664228188223
  covers := by decide +kernel

/-- Pivot code 265856443580544. -/
def p189 : MaskPattern where
  pivot := ![0, 1, 6, 55, 56, 57, 60]
  increasing := by decide +kernel
  mask := 10751367260834856933026895844436740945268587664229793855
  covers := by decide +kernel

/-- Pivot code 265890803253376. -/
def p190 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 58, 60]
  increasing := by decide +kernel
  mask := 10898031873144287702674472024769485378857099806780686847
  covers := by decide +kernel

/-- Pivot code 265890803269760. -/
def p191 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 58, 60]
  increasing := by decide +kernel
  mask := 10898031873144287702674472024769485378857099806780689983
  covers := by decide +kernel

/-- Pivot code 265890803269889. -/
def p192 : MaskPattern where
  pivot := ![1, 2, 3, 55, 56, 58, 60]
  increasing := by decide +kernel
  mask := 10898031873144287702674472024769485378857099806780690424
  covers := by decide +kernel

/-- Pivot code 265890803286144. -/
def p193 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 58, 60]
  increasing := by decide +kernel
  mask := 10898031873144287702674472024769485378857099806780715071
  covers := by decide +kernel

/-- Pivot code 265891071688832. -/
def p194 : MaskPattern where
  pivot := ![0, 1, 2, 55, 57, 58, 60]
  increasing := by decide +kernel
  mask := 10916364949682966548880419047311078433055663824599777791
  covers := by decide +kernel

/-- Pivot code 265891071705344. -/
def p195 : MaskPattern where
  pivot := ![0, 2, 3, 55, 57, 58, 60]
  increasing := by decide +kernel
  mask := 10916364949682966548880419047311078433055663824599781319
  covers := by decide +kernel

/-- Pivot code 265925162991744. -/
def p196 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 59, 60]
  increasing := by decide +kernel
  mask := 12071348771619733859855081467431440847565196947202507263
  covers := by decide +kernel

/-- Pivot code 265925163008128. -/
def p197 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 59, 60]
  increasing := by decide +kernel
  mask := 12071348771619733859855081467431440847565196947202510399
  covers := by decide +kernel

/-- Pivot code 270254490026112. -/
def p198 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 61]
  increasing := by decide +kernel
  mask := 85843648763263410992585900174801890942586804651224465919
  covers := by decide +kernel

/-- Pivot code 270254490042496. -/
def p199 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 57, 61]
  increasing := by decide +kernel
  mask := 85843648763263410992585900174801890942586804651224469055
  covers := by decide +kernel

/-- Pivot code 270254490042625. -/
def p200 : MaskPattern where
  pivot := ![1, 2, 3, 55, 56, 57, 61]
  increasing := by decide +kernel
  mask := 85843648763263410992585900174801890942586804651224469496
  covers := by decide +kernel

/-- Pivot code 270288849764480. -/
def p201 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 58, 61]
  increasing := by decide +kernel
  mask := 85990313375572841762233476355134635376175316793777193471
  covers := by decide +kernel

/-- Pivot code 270288849780864. -/
def p202 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 58, 61]
  increasing := by decide +kernel
  mask := 85990313375572841762233476355134635376175316793777196607
  covers := by decide +kernel

/-- Pivot code 270323209535616. -/
def p203 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 59, 61]
  increasing := by decide +kernel
  mask := 87163630274048287919414085797796590844883413934199042111
  covers := by decide +kernel

/-- Pivot code 270357569290368. -/
def p204 : MaskPattern where
  pivot := ![0, 1, 5, 55, 56, 60, 61]
  increasing := by decide +kernel
  mask := 96550165461851857176858961339092234594548191057573806143
  covers := by decide +kernel

/-- Pivot code 274652536537216. -/
def p205 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 62]
  increasing := by decide +kernel
  mask := 686581900782691843469057934817723090921132540547196518911
  covers := by decide +kernel

/-- Pivot code 274686896275584. -/
def p206 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 58, 62]
  increasing := by decide +kernel
  mask := 686728565395001274238705510998055835354721052689749246463
  covers := by decide +kernel

/-- Pivot code 274755615752320. -/
def p207 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 60, 62]
  increasing := by decide +kernel
  mask := 697288417481280289653330995982013434573093926953545630207
  covers := by decide +kernel

/-- Pivot code 279050583048320. -/
def p208 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 63]
  increasing := by decide +kernel
  mask := 5492487916938119303280834211961092690749498427714972942847
  covers := by decide +kernel

/-- Pivot code 441778303959168. -/
def p209 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 100]
  increasing := by decide +kernel
  mask := 14259251834341402603879119818865647127384177230435188678971449799865245758280770752226525695
  covers := by decide +kernel

/-- Pivot code 441812663713920. -/
def p210 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 58, 100]
  increasing := by decide +kernel
  mask := 14259251834341402603879119818865647127530841842744619448619025980197990191869282894779256383
  covers := by decide +kernel

/-- Pivot code 441812932149504. -/
def p211 : MaskPattern where
  pivot := ![0, 2, 3, 55, 57, 58, 100]
  increasing := by decide +kernel
  mask := 14259251834341402603879119818865647127549174919283298294824973002739583246067846912598347719
  covers := by decide +kernel

/-- Pivot code 441847023468672. -/
def p212 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 59, 100]
  increasing := by decide +kernel
  mask := 14259251834341402603879119818865647128704158741220065605799635422859945660577380035201101887
  covers := by decide +kernel

/-- Pivot code 446176350470272. -/
def p213 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 101]
  increasing := by decide +kernel
  mask := 114074014674731220831032958550925177018906128520066064960142331818229929446684269355212997119
  covers := by decide +kernel

/-- Pivot code 446210710225024. -/
def p214 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 58, 101]
  increasing := by decide +kernel
  mask := 114074014674731220831032958550925177019052793132375495729789907998562673880272781497765727807
  covers := by decide +kernel

/-- Pivot code 446245069979776. -/
def p215 : MaskPattern where
  pivot := ![0, 1, 4, 55, 56, 59, 101]
  increasing := by decide +kernel
  mask := 114074014674731220831032958550925177020226110030850941886970517441224629348980878638187573311
  covers := by decide +kernel

/-- Pivot code 450574396981376. -/
def p216 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 102]
  increasing := by decide +kernel
  mask := 912592117397849766648263668407401416151081738837113075209509387965147398953912258179104768511
  covers := by decide +kernel

/-- Pivot code 450608756736128. -/
def p217 : MaskPattern where
  pivot := ![0, 1, 3, 55, 56, 58, 102]
  increasing := by decide +kernel
  mask := 912592117397849766648263668407401416151228403449422505979156964145480143387500770321657499199
  covers := by decide +kernel

/-- Pivot code 463768536514688. -/
def p218 : MaskPattern where
  pivot := ![0, 1, 2, 55, 56, 57, 105]
  increasing := by decide +kernel
  mask := 467247164107699080523910998224589525069341638163992567060839870177764949591175057731331899261439
  covers := by decide +kernel

/-- A certified candidate for every code; shape checks verify its suitability. -/
def get (code : ℕ) : MaskPattern :=
  (if code < 198119602045056 then (if code < 44187974140032 then (if code < 39789657096320 then (if code < 35391881134336 then (if code < 30993834623232 then (if code < 30993832509568 then (if code < 30959204335744 then p000 else (if code < 30993564074112 then p001 else p002)) else (if code < 30993834606720 then p003 else (if code < 30993834623104 then p004 else p005))) else (if code < 35391610585216 then (if code < 30993834623233 then p006 else (if code < 35357250846848 then p007 else p008)) else (if code < 35391881117824 then (if code < 35391879020672 then p009 else p010) else (if code < 35391881134208 then p011 else p012)))) else (if code < 35426507194496 then (if code < 35426238759040 then (if code < 35391881134337 then p013 else (if code < 35425970323584 then p014 else p015)) else (if code < 35426240872576 then (if code < 35426240856192 then p016 else p017) else (if code < 35426240872704 then p018 else p019))) else (if code < 35426511388800 then (if code < 35426509291648 then p020 else (if code < 35426509308032 then p021 else p022)) else (if code < 35426511421568 then (if code < 35426511405184 then p023 else p024) else (if code < 39755297357952 then p025 else p026))))) else (if code < 39824557899904 then (if code < 39824016834688 then (if code < 39789927645312 then (if code < 39789925531776 then p027 else (if code < 39789927628928 then p028 else p029)) else (if code < 39789927645440 then p030 else (if code < 39789927645441 then p031 else p032))) else (if code < 39824287383680 then (if code < 39824285270144 then p033 else (if code < 39824287367296 then p034 else p035)) else (if code < 39824555802752 then (if code < 39824553705600 then p036 else p037) else (if code < 39824555819136 then p038 else p039)))) else (if code < 39858913443968 then (if code < 39858645008512 then (if code < 39824557932800 then p040 else (if code < 39858376573056 then p041 else p042)) else (if code < 39858647122048 then (if code < 39858647105664 then p043 else p044) else (if code < 39858647122176 then p045 else p046))) else (if code < 39859183976576 then (if code < 39858917638272 then p047 else (if code < 39859181879424 then p048 else p049)) else (if code < 44187703607424 then (if code < 44153343869056 then p050 else p051) else (if code < 44187972042880 then p052 else p053)))))) else (if code < 48620380405888 then (if code < 44256691519616 then (if code < 44222333878400 then (if code < 44187974156545 then (if code < 44187974156416 then p054 else (if code < 44187974156544 then p055 else p056)) else (if code < 44222063345792 then p057 else (if code < 44222331781248 then p058 else p059))) else (if code < 44222333894913 then (if code < 44222333894784 then p060 else (if code < 44222333894912 then p061 else p062)) else (if code < 44222602313856 then (if code < 44222600216704 then p063 else p064) else (if code < 44256423084160 then p065 else p066)))) else (if code < 48585750118528 then (if code < 44256959955072 then (if code < 44256693616768 then p067 else (if code < 44256693633152 then p068 else p069)) else (if code < 44291053355136 then (if code < 44290782822528 then p070 else p071) else (if code < 48551390380160 then p072 else p073))) else (if code < 48586020667648 then (if code < 48586018553984 then p074 else (if code < 48586020651136 then p075 else p076)) else (if code < 48620378292352 then (if code < 48620109856896 then p077 else p078) else (if code < 48620380389504 then p079 else p080))))) else (if code < 53052516106368 then (if code < 52949436891264 then (if code < 48654738030720 then (if code < 48620646727808 then p081 else (if code < 48654469595264 then p082 else p083)) else (if code < 48688829333632 then (if code < 48654740144384 then p084 else p085) else (if code < 48689099866240 then p086 else p087))) else (if code < 52984067162240 then (if code < 52983796629632 then p088 else (if code < 52984065065088 then p089 else p090)) else (if code < 53018424803456 then (if code < 53018156368000 then p091 else p092) else (if code < 53018426900608 then p093 else p094)))) else (if code < 61779889651840 then (if code < 57382111576192 then (if code < 57347483402368 then p095 else (if code < 57381843140736 then p096 else p097)) else (if code < 57416473411712 then (if code < 57416202879104 then p098 else p099) else (if code < 61745529913472 then p100 else p101))) else (if code < 198084971757696 then (if code < 66143576424576 then p102 else (if code < 66177936162944 then p103 else p104)) else (if code < 198119599931520 then (if code < 198119331496064 then p105 else p106) else (if code < 198119602028672 then p107 else p108))))))) else (if code < 257060350574720 then (if code < 202586634354816 then (if code < 198222681243776 then (if code < 198188050972800 then (if code < 198153961767040 then (if code < 198153691234432 then p109 else (if code < 198153959669888 then p110 else p111)) else (if code < 198153961783424 then p112 else (if code < 198154228105344 then p113 else p114))) else (if code < 198188321521792 then (if code < 198188319408256 then p115 else (if code < 198188321505408 then p116 else p117)) else (if code < 198222410711168 then (if code < 198188587843712 then p118 else p119) else (if code < 198222679146624 then p120 else p121)))) else (if code < 202517648539776 then (if code < 198257038884992 then (if code < 198222681260160 then p122 else (if code < 198256770449536 then p123 else p124)) else (if code < 202517378007168 then (if code < 202483018268800 then p125 else p126) else (if code < 202517646442624 then p127 else p128))) else (if code < 202552006180992 then (if code < 202517648556160 then p129 else (if code < 202551737745536 then p130 else p131)) else (if code < 202586097483904 then (if code < 202552008278144 then p132 else p133) else (if code < 202586365919360 then p134 else p135))))) else (if code < 257060350509184 then (if code < 206949784256640 then (if code < 206881064779904 then (if code < 202620457222272 then p136 else (if code < 202620725657728 then p137 else p138)) else (if code < 206915692953728 then (if code < 206915424518272 then p139 else p140) else (if code < 206915695050880 then p141 else p142))) else (if code < 211313471029376 then (if code < 206950052692096 then p143 else (if code < 211279111291008 then p144 else p145)) else (if code < 215677157802112 then (if code < 211347830767744 then p146 else p147) else (if code < 257060350492800 then p148 else p149)))) else (if code < 257060350541952 then (if code < 257060350525568 then (if code < 257060350509312 then p150 else (if code < 257060350509313 then p151 else p152)) else (if code < 257060350525697 then (if code < 257060350525696 then p153 else p154) else (if code < 257060350525824 then p155 else p156))) else (if code < 257060350542208 then (if code < 257060350542080 then p157 else (if code < 257060350542081 then p158 else p159)) else (if code < 257060350558464 then (if code < 257060350558336 then p160 else p161) else (if code < 257060350558592 then p162 else p163)))))) else (if code < 265890803269760 then (if code < 261492756758784 then (if code < 261458397036800 then (if code < 261458397020288 then (if code < 257060350591232 then p164 else (if code < 261458397003904 then p165 else p166)) else (if code < 261458397020416 then p167 else (if code < 261458397036672 then p168 else p169))) else (if code < 261458397053056 then (if code < 261458397036801 then p170 else (if code < 261458397036928 then p171 else p172)) else (if code < 261492756742272 then (if code < 261458397069440 then p173 else p174) else (if code < 261492756758656 then p175 else p176)))) else (if code < 265856443515008 then (if code < 261493025177728 then (if code < 261492756775040 then p177 else (if code < 261492756791424 then p178 else p179)) else (if code < 261493025194240 then (if code < 261493025194112 then p180 else p181) else (if code < 261493027274880 then p182 else p183))) else (if code < 265856443547904 then (if code < 265856443531392 then p184 else (if code < 265856443547776 then p185 else p186)) else (if code < 265856443580544 then (if code < 265856443564160 then p187 else p188) else (if code < 265890803253376 then p189 else p190))))) else (if code < 274652536537216 then (if code < 270254490026112 then (if code < 265891071688832 then (if code < 265890803269889 then p191 else (if code < 265890803286144 then p192 else p193)) else (if code < 265925162991744 then (if code < 265891071705344 then p194 else p195) else (if code < 265925163008128 then p196 else p197))) else (if code < 270288849764480 then (if code < 270254490042496 then p198 else (if code < 270254490042625 then p199 else p200)) else (if code < 270323209535616 then (if code < 270288849780864 then p201 else p202) else (if code < 270357569290368 then p203 else p204)))) else (if code < 441847023468672 then (if code < 279050583048320 then (if code < 274686896275584 then p205 else (if code < 274755615752320 then p206 else p207)) else (if code < 441812663713920 then (if code < 441778303959168 then p208 else p209) else (if code < 441812932149504 then p210 else p211))) else (if code < 446245069979776 then (if code < 446176350470272 then p212 else (if code < 446210710225024 then p213 else p214)) else (if code < 450608756736128 then (if code < 450574396981376 then p215 else p216) else (if code < 463768536514688 then p217 else p218))))))))

end Lyons.OrderCertificate.PlaneOrbitData.PivotPatterns
