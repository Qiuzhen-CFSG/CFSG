module

public import Theory.SpecificGroups.Lyons.Atlas111LocalPresentationSetup
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationShared
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationFirst
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLast

/-!
# Assembly of the local presentation relations

Shared subwords compress the 7415-letter input into 289 products. Each
product is supplied by an explicit matrix-arithmetic contract. Concatenation
and the free-group universal property then recover the original fixed relators.
The kernel-checked numerical certificates discharge all four contracts, proving
the relations on the exact ATLAS program outputs without identification, order,
or simplicity assumptions.

Source and reproducible candidate generation: `Atlas111LocalRelationSource/`.
-/

namespace Lyons.RelationCertificate
open OrderCertificate

private def letter (c : Char) : Bool × Bool :=
  if c = 'a' then (false, true) else
  if c = 'A' then (false, false) else
  if c = 'b' then (true, true) else (true, false)

private def wordMatrix (w : List Char) : AtlasMatrix :=
  ↑(FreeGroup.lift localMatrixAssignment (FreeGroup.mk (w.map letter)))

private theorem wordMatrix_append (u v : List Char) :
    wordMatrix (u ++ v) = wordMatrix u * wordMatrix v := by
  simp only [wordMatrix, List.map_append, FreeGroup.lift_mk, List.prod_append,
    Units.val_mul]

private theorem relation_of_wordMatrix (i : Fin 22)
    (h : wordMatrix (G2Five.AtlasPresentation.word i).toList = 1) :
    FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator i) = 1 := by
  apply Units.ext
  exact h

private theorem wordMatrix_a : wordMatrix ['a'] = ↑(localMatrixAssignment false) := by
  simp [wordMatrix, letter, FreeGroup.lift_mk]
private theorem wordMatrix_b : wordMatrix ['b'] = ↑(localMatrixAssignment true) := by
  simp [wordMatrix, letter, FreeGroup.lift_mk]
private theorem wordMatrix_B : wordMatrix ['B'] = ↑((localMatrixAssignment true)⁻¹) := by
  simp [wordMatrix, letter, FreeGroup.lift_mk]

private def wa : List Char := ['a']
private def wb : List Char := ['b']
private def wB : List Char := ['B']

private def wg0 : List Char := wa ++ wb
private def wg1 : List Char := wa ++ wB
private def wg2 : List Char := wg0 ++ wg1
private def wg3 : List Char := wg2 ++ wg2
private def wg4 : List Char := wg2 ++ wg1
private def wg5 : List Char := wg0 ++ wg3
private def wg6 : List Char := wg0 ++ wg4
private def wg7 : List Char := wg6 ++ wg3
private def wg8 : List Char := wg2 ++ wg7
private def wg9 : List Char := wg1 ++ wg3
private def wg10 : List Char := wg7 ++ wg3
private def wg11 : List Char := wg5 ++ wg10
private def wg12 : List Char := wg11 ++ wg8
private def wg13 : List Char := wg5 ++ wg3
private def wg14 : List Char := wg0 ++ wg2
private def wg15 : List Char := wg4 ++ wg3
private def wg16 : List Char := wg12 ++ wg9
private def wg17 : List Char := wg16 ++ wg13
private def wg18 : List Char := wg5 ++ wg1
private def wg19 : List Char := wg12 ++ wg1
private def wg20 : List Char := wg9 ++ wg1
private def wg21 : List Char := wg17 ++ wg4
private def wg22 : List Char := wg4 ++ wg2
private def wg23 : List Char := wg14 ++ wg14
private def wg24 : List Char := wg5 ++ wg2
private def wg25 : List Char := wg0 ++ wg8
private def wg26 : List Char := wg15 ++ wg19
private def wg27 : List Char := wg14 ++ wg18
private def wg28 : List Char := wg6 ++ wg4
private def wg29 : List Char := wg15 ++ wg1
private def wg30 : List Char := wg4 ++ wg4
private def wg31 : List Char := wg5 ++ wg20
private def wg32 : List Char := wg0 ++ wg0
private def wg33 : List Char := wg14 ++ wg6
private def wg34 : List Char := wg13 ++ wg1
private def wg35 : List Char := wg6 ++ wg2
private def wg36 : List Char := wg5 ++ wg4
private def wg37 : List Char := wg13 ++ wg26
private def wg38 : List Char := wg3 ++ wg3
private def wg39 : List Char := wg9 ++ wg19
private def wg40 : List Char := wg21 ++ wg31
private def wg41 : List Char := wg8 ++ wg3
private def wg42 : List Char := wg15 ++ wg20
private def wg43 : List Char := wg33 ++ wg27
private def wg44 : List Char := wg13 ++ wg3
private def wg45 : List Char := wg5 ++ wg5
private def wg46 : List Char := wg12 ++ wg22
private def wg47 : List Char := wg2 ++ wg6
private def wg48 : List Char := wg18 ++ wg37
private def wg49 : List Char := wb ++ wg9
private def wg50 : List Char := wg22 ++ wg43
private def wg51 : List Char := wg4 ++ wg6
private def wg52 : List Char := wg21 ++ wg4
private def wg53 : List Char := wg5 ++ wg14
private def wg54 : List Char := wg1 ++ wg5
private def wg55 : List Char := wg8 ++ wg9
private def wg56 : List Char := wg14 ++ wg5
private def wg57 : List Char := wg1 ++ wg2
private def wg58 : List Char := wg9 ++ wg46
private def wg59 : List Char := wg5 ++ wg19
private def wg60 : List Char := wg3 ++ wg20
private def wg61 : List Char := wg41 ++ wg26
private def wg62 : List Char := wg5 ++ wg7
private def wg63 : List Char := wg62 ++ wg30
private def wg64 : List Char := wg63 ++ wg16
private def wg65 : List Char := wg6 ++ wg35
private def wg66 : List Char := wg21 ++ wg48
private def wg67 : List Char := wg36 ++ wg28
private def wg68 : List Char := wg67 ++ wg29
private def wg69 : List Char := wg68 ++ wg30
private def wg70 : List Char := wb ++ wb
private def wg71 : List Char := wg32 ++ wg32
private def wg72 : List Char := wg38 ++ wg38
private def wg73 : List Char := wg24 ++ wg5
private def wg74 : List Char := wg73 ++ wg24
private def wg75 : List Char := wg27 ++ wg50
private def wg76 : List Char := wg51 ++ wg22
private def wg77 : List Char := wg2 ++ wg14
private def wg78 : List Char := wg21 ++ wg23
private def wg79 : List Char := wg44 ++ wg39
private def wg80 : List Char := wg25 ++ wg54
private def wg81 : List Char := wg29 ++ wg52
private def wg82 : List Char := wg1 ++ wg4
private def wg83 : List Char := wg13 ++ wg39
private def wg84 : List Char := wg53 ++ wa
private def wg85 : List Char := wg28 ++ wg17
private def wg86 : List Char := wg18 ++ wg2
private def wg87 : List Char := wg19 ++ wg4
private def wg88 : List Char := wg87 ++ wg10
private def wg89 : List Char := wg88 ++ wg57
private def wg90 : List Char := wg24 ++ wg23
private def wg91 : List Char := wg90 ++ wg45
private def wg92 : List Char := wg23 ++ wg56
private def wg93 : List Char := wg92 ++ wg23
private def wg94 : List Char := wg93 ++ wg6
private def wg95 : List Char := wg5 ++ wg35
private def wg96 : List Char := wg95 ++ wg18
private def wg97 : List Char := wg96 ++ wg22
private def wg98 : List Char := wg97 ++ wg13
private def wg99 : List Char := wg98 ++ wg58
private def wg100 : List Char := wg59 ++ wg25
private def wg101 : List Char := wg60 ++ wg17
private def wg102 : List Char := wg33 ++ wg0
private def wg103 : List Char := wg5 ++ wg41
private def wg104 : List Char := wg103 ++ wg55
private def wg105 : List Char := wg5 ++ wg65
private def wg106 : List Char := wg105 ++ wg5
private def wg107 : List Char := wg106 ++ wg25
private def wg108 : List Char := wg107 ++ wg2
private def wg109 : List Char := wg108 ++ wg64
private def wg110 : List Char := wg109 ++ wg6
private def wg111 : List Char := wg5 ++ wg31
private def wg112 : List Char := wg69 ++ wg15
private def wr0p0 : List Char := wa ++ wa
private def wr1p0 : List Char := wg70 ++ wb
private def wr2p0 : List Char := wg71 ++ wg32
private def wr2p1 : List Char := wr2p0 ++ wg0
private def wr3p0 : List Char := wg49 ++ wg72
private def wr3p1 : List Char := wr3p0 ++ wg38
private def wr3p2 : List Char := wr3p1 ++ wa
private def wr4p0 : List Char := wg49 ++ wg2
private def wr4p1 : List Char := wr4p0 ++ wg74
private def wr4p2 : List Char := wr4p1 ++ wg25
private def wr4p3 : List Char := wr4p2 ++ wg15
private def wr4p4 : List Char := wr4p3 ++ wg42
private def wr4p5 : List Char := wr4p4 ++ wg14
private def wr4p6 : List Char := wr4p5 ++ wg0
private def wr4p7 : List Char := wr4p6 ++ wa
private def wr5p0 : List Char := wg75 ++ wg76
private def wr5p1 : List Char := wr5p0 ++ wg75
private def wr5p2 : List Char := wr5p1 ++ wg50
private def wr5p3 : List Char := wr5p2 ++ wg76
private def wr6p0 : List Char := wg77 ++ wg34
private def wr6p1 : List Char := wr6p0 ++ wg16
private def wr6p2 : List Char := wr6p1 ++ wg24
private def wr6p3 : List Char := wr6p2 ++ wg35
private def wr6p4 : List Char := wr6p3 ++ wg52
private def wr6p5 : List Char := wr6p4 ++ wg53
private def wr7p0 : List Char := wg28 ++ wg78
private def wr7p1 : List Char := wr7p0 ++ wg24
private def wr7p2 : List Char := wr7p1 ++ wg79
private def wr7p3 : List Char := wr7p2 ++ wg80
private def wr8p0 : List Char := wg49 ++ wg81
private def wr8p1 : List Char := wr8p0 ++ wg43
private def wr8p2 : List Char := wr8p1 ++ wg4
private def wr8p3 : List Char := wr8p2 ++ wg7
private def wr8p4 : List Char := wr8p3 ++ wg82
private def wr8p5 : List Char := wr8p4 ++ wg83
private def wr8p6 : List Char := wr8p5 ++ wg84
private def wr9p0 : List Char := wg74 ++ wg85
private def wr9p1 : List Char := wr9p0 ++ wg42
private def wr9p2 : List Char := wr9p1 ++ wg5
private def wr9p3 : List Char := wr9p2 ++ wg55
private def wr9p4 : List Char := wr9p3 ++ wg20
private def wr9p5 : List Char := wr9p4 ++ wg4
private def wr9p6 : List Char := wr9p5 ++ wg81
private def wr9p7 : List Char := wr9p6 ++ wg56
private def wr10p0 : List Char := wg3 ++ wg4
private def wr10p1 : List Char := wr10p0 ++ wg86
private def wr10p2 : List Char := wr10p1 ++ wg28
private def wr10p3 : List Char := wr10p2 ++ wg89
private def wr10p4 : List Char := wr10p3 ++ wg91
private def wr10p5 : List Char := wr10p4 ++ wg13
private def wr10p6 : List Char := wr10p5 ++ wg79
private def wr10p7 : List Char := wr10p6 ++ wg6
private def wr10p8 : List Char := wr10p7 ++ wg6
private def wr10p9 : List Char := wr10p8 ++ wg94
private def wr10p10 : List Char := wr10p9 ++ wg0
private def wr11p0 : List Char := wg91 ++ wg5
private def wr11p1 : List Char := wr11p0 ++ wg34
private def wr11p2 : List Char := wr11p1 ++ wg17
private def wr11p3 : List Char := wr11p2 ++ wg1
private def wr11p4 : List Char := wr11p3 ++ wg14
private def wr11p5 : List Char := wr11p4 ++ wg13
private def wr11p6 : List Char := wr11p5 ++ wg28
private def wr11p7 : List Char := wr11p6 ++ wg40
private def wr11p8 : List Char := wr11p7 ++ wg89
private def wr12p0 : List Char := wg3 ++ wg19
private def wr12p1 : List Char := wr12p0 ++ wg99
private def wr12p2 : List Char := wr12p1 ++ wg59
private def wr12p3 : List Char := wr12p2 ++ wg99
private def wr12p4 : List Char := wr12p3 ++ wg0
private def wr13p0 : List Char := wg44 ++ wg58
private def wr13p1 : List Char := wr13p0 ++ wg100
private def wr13p2 : List Char := wr13p1 ++ wg42
private def wr13p3 : List Char := wr13p2 ++ wg30
private def wr13p4 : List Char := wr13p3 ++ wg13
private def wr13p5 : List Char := wr13p4 ++ wg15
private def wr13p6 : List Char := wr13p5 ++ wg46
private def wr13p7 : List Char := wr13p6 ++ wg100
private def wr13p8 : List Char := wr13p7 ++ wg3
private def wr13p9 : List Char := wr13p8 ++ wg82
private def wr13p10 : List Char := wr13p9 ++ wg24
private def wr14p0 : List Char := wg9 ++ wg101
private def wr14p1 : List Char := wr14p0 ++ wg47
private def wr14p2 : List Char := wr14p1 ++ wg61
private def wr14p3 : List Char := wr14p2 ++ wg6
private def wr14p4 : List Char := wr14p3 ++ wg10
private def wr14p5 : List Char := wr14p4 ++ wg54
private def wr14p6 : List Char := wr14p5 ++ wg8
private def wr14p7 : List Char := wr14p6 ++ wg94
private def wr14p8 : List Char := wr14p7 ++ wg36
private def wr14p9 : List Char := wr14p8 ++ wg86
private def wr14p10 : List Char := wr14p9 ++ wg85
private def wr14p11 : List Char := wr14p10 ++ wg57
private def wr15p0 : List Char := wg9 ++ wg64
private def wr15p1 : List Char := wr15p0 ++ wg18
private def wr15p2 : List Char := wr15p1 ++ wg47
private def wr15p3 : List Char := wr15p2 ++ wg40
private def wr15p4 : List Char := wr15p3 ++ wg40
private def wr15p5 : List Char := wr15p4 ++ wg78
private def wr15p6 : List Char := wr15p5 ++ wg102
private def wr16p0 : List Char := wg60 ++ wg21
private def wr16p1 : List Char := wr16p0 ++ wg6
private def wr16p2 : List Char := wr16p1 ++ wg8
private def wr16p3 : List Char := wr16p2 ++ wg104
private def wr16p4 : List Char := wr16p3 ++ wg13
private def wr16p5 : List Char := wr16p4 ++ wg47
private def wr16p6 : List Char := wr16p5 ++ wg65
private def wr16p7 : List Char := wr16p6 ++ wg6
private def wr16p8 : List Char := wr16p7 ++ wg66
private def wr16p9 : List Char := wr16p8 ++ wg13
private def wr16p10 : List Char := wr16p9 ++ wg20
private def wr16p11 : List Char := wr16p10 ++ wg0
private def wr17p0 : List Char := wg1 ++ wg18
private def wr17p1 : List Char := wr17p0 ++ wg5
private def wr17p2 : List Char := wr17p1 ++ wg22
private def wr17p3 : List Char := wr17p2 ++ wg25
private def wr17p4 : List Char := wr17p3 ++ wg104
private def wr17p5 : List Char := wr17p4 ++ wg34
private def wr17p6 : List Char := wr17p5 ++ wg2
private def wr17p7 : List Char := wr17p6 ++ wg27
private def wr17p8 : List Char := wr17p7 ++ wg4
private def wr17p9 : List Char := wr17p8 ++ wg36
private def wr17p10 : List Char := wr17p9 ++ wg69
private def wr17p11 : List Char := wr17p10 ++ wg51
private def wr17p12 : List Char := wr17p11 ++ wg6
private def wr17p13 : List Char := wr17p12 ++ wg17
private def wr17p14 : List Char := wr17p13 ++ wg42
private def wr17p15 : List Char := wr17p14 ++ wg4
private def wr17p16 : List Char := wr17p15 ++ wg83
private def wr17p17 : List Char := wr17p16 ++ wg80
private def wr18p0 : List Char := wB ++ wg36
private def wr18p1 : List Char := wr18p0 ++ wg110
private def wr18p2 : List Char := wr18p1 ++ wg27
private def wr18p3 : List Char := wr18p2 ++ wg61
private def wr18p4 : List Char := wr18p3 ++ wg45
private def wr18p5 : List Char := wr18p4 ++ wg18
private def wr18p6 : List Char := wr18p5 ++ wg61
private def wr18p7 : List Char := wr18p6 ++ wg5
private def wr18p8 : List Char := wr18p7 ++ wg48
private def wr18p9 : List Char := wr18p8 ++ wg84
private def wr19p0 : List Char := wB ++ wg6
private def wr19p1 : List Char := wr19p0 ++ wg110
private def wr19p2 : List Char := wr19p1 ++ wg44
private def wr19p3 : List Char := wr19p2 ++ wg29
private def wr19p4 : List Char := wr19p3 ++ wg66
private def wr19p5 : List Char := wr19p4 ++ wg34
private def wr19p6 : List Char := wr19p5 ++ wg4
private def wr19p7 : List Char := wr19p6 ++ wg14
private def wr19p8 : List Char := wr19p7 ++ wg37
private def wr19p9 : List Char := wr19p8 ++ wg34
private def wr19p10 : List Char := wr19p9 ++ wg77
private def wr19p11 : List Char := wr19p10 ++ wa
private def wr20p0 : List Char := wg4 ++ wg25
private def wr20p1 : List Char := wr20p0 ++ wg10
private def wr20p2 : List Char := wr20p1 ++ wg39
private def wr20p3 : List Char := wr20p2 ++ wg111
private def wr20p4 : List Char := wr20p3 ++ wg17
private def wr20p5 : List Char := wr20p4 ++ wg47
private def wr20p6 : List Char := wr20p5 ++ wg8
private def wr20p7 : List Char := wr20p6 ++ wg34
private def wr20p8 : List Char := wr20p7 ++ wg40
private def wr20p9 : List Char := wr20p8 ++ wg66
private def wr20p10 : List Char := wr20p9 ++ wg102
private def wr21p0 : List Char := wg4 ++ wg37
private def wr21p1 : List Char := wr21p0 ++ wg111
private def wr21p2 : List Char := wr21p1 ++ wg40
private def wr21p3 : List Char := wr21p2 ++ wg17
private def wr21p4 : List Char := wr21p3 ++ wg29
private def wr21p5 : List Char := wr21p4 ++ wg29
private def wr21p6 : List Char := wr21p5 ++ wg18
private def wr21p7 : List Char := wr21p6 ++ wg112
private def wr21p8 : List Char := wr21p7 ++ wg101
private def wr21p9 : List Char := wr21p8 ++ wg15
private def wr21p10 : List Char := wr21p9 ++ wg3
private def wr21p11 : List Char := wr21p10 ++ wg1
private def wr21p12 : List Char := wr21p11 ++ wg112
private def wr21p13 : List Char := wr21p12 ++ wg2

private theorem allFin22 {P : Fin 22 → Prop}
    (h0 : P 0)
    (h1 : P 1)
    (h2 : P 2)
    (h3 : P 3)
    (h4 : P 4)
    (h5 : P 5)
    (h6 : P 6)
    (h7 : P 7)
    (h8 : P 8)
    (h9 : P 9)
    (h10 : P 10)
    (h11 : P 11)
    (h12 : P 12)
    (h13 : P 13)
    (h14 : P 14)
    (h15 : P 15)
    (h16 : P 16)
    (h17 : P 17)
    (h18 : P 18)
    (h19 : P 19)
    (h20 : P 20)
    (h21 : P 21)
    : ∀ i, P i :=
  (Fin.cases h0
    (Fin.cases h1
    (Fin.cases h2
    (Fin.cases h3
    (Fin.cases h4
    (Fin.cases h5
    (Fin.cases h6
    (Fin.cases h7
    (Fin.cases h8
    (Fin.cases h9
    (Fin.cases h10
    (Fin.cases h11
    (Fin.cases h12
    (Fin.cases h13
    (Fin.cases h14
    (Fin.cases h15
    (Fin.cases h16
    (Fin.cases h17
    (Fin.cases h18
    (Fin.cases h19
    (Fin.cases h20
    (Fin.cases h21
    (fun i => Fin.elim0 i)))))))))))))))))))))))

private theorem literal_word0 :
    (G2Five.AtlasPresentation.word 0).toList = wr0p0 := by decide +kernel

private theorem literal_word1 :
    (G2Five.AtlasPresentation.word 1).toList = wr1p0 := by decide +kernel

private theorem literal_word2 :
    (G2Five.AtlasPresentation.word 2).toList = wr2p1 := by decide +kernel

private theorem literal_word3 :
    (G2Five.AtlasPresentation.word 3).toList = wr3p2 := by decide +kernel

private theorem literal_word4 :
    (G2Five.AtlasPresentation.word 4).toList = wr4p7 := by decide +kernel

private theorem literal_word5 :
    (G2Five.AtlasPresentation.word 5).toList = wr5p3 := by decide +kernel

private theorem literal_word6 :
    (G2Five.AtlasPresentation.word 6).toList = wr6p5 := by decide +kernel

private theorem literal_word7 :
    (G2Five.AtlasPresentation.word 7).toList = wr7p3 := by decide +kernel

private theorem literal_word8 :
    (G2Five.AtlasPresentation.word 8).toList = wr8p6 := by decide +kernel

private theorem literal_word9 :
    (G2Five.AtlasPresentation.word 9).toList = wr9p7 := by decide +kernel

private theorem literal_word10 :
    (G2Five.AtlasPresentation.word 10).toList = wr10p10 := by decide +kernel

private theorem literal_word11 :
    (G2Five.AtlasPresentation.word 11).toList = wr11p8 := by decide +kernel

private theorem literal_word12 :
    (G2Five.AtlasPresentation.word 12).toList = wr12p4 := by decide +kernel

private theorem literal_word13 :
    (G2Five.AtlasPresentation.word 13).toList = wr13p10 := by decide +kernel

private theorem literal_word14 :
    (G2Five.AtlasPresentation.word 14).toList = wr14p11 := by decide +kernel

private theorem literal_word15 :
    (G2Five.AtlasPresentation.word 15).toList = wr15p6 := by decide +kernel

private theorem literal_word16 :
    (G2Five.AtlasPresentation.word 16).toList = wr16p11 := by decide +kernel

private theorem literal_word17 :
    (G2Five.AtlasPresentation.word 17).toList = wr17p17 := by decide +kernel

private theorem literal_word18 :
    (G2Five.AtlasPresentation.word 18).toList = wr18p9 := by decide +kernel

private theorem literal_word19 :
    (G2Five.AtlasPresentation.word 19).toList = wr19p11 := by decide +kernel

private theorem literal_word20 :
    (G2Five.AtlasPresentation.word 20).toList = wr20p10 := by decide +kernel

private theorem literal_word21 :
    (G2Five.AtlasPresentation.word 21).toList = wr21p13 := by decide +kernel

end Lyons.RelationCertificate

namespace Lyons.OrderCertificate
open RelationCertificate

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
/-- Matrix arithmetic suffices to establish the exact fixed presentation relations. -/
private theorem assemble (M : Fin 261 → AtlasMatrix)
    (hseed : M 0 = 1 ∧ M 1 = ↑(localMatrixAssignment false) ∧
      M 2 = ↑(localMatrixAssignment true) ∧ M 3 = ↑((localMatrixAssignment true)⁻¹))
    (hshared : ∀ i, let e := sharedSpec i; M e.1 * M e.2.1 = M e.2.2)
    (hfirst : ∀ i, let e := firstSpec i; M e.1 * M e.2.1 = M e.2.2)
    (hlast : ∀ i, let e := lastSpec i; M e.1 * M e.2.1 = M e.2.2) :
    LocalPresentationRelations := by
  have ha : wordMatrix wa = M 1 := wordMatrix_a.trans hseed.2.1.symm
  have hb : wordMatrix wb = M 2 := wordMatrix_b.trans hseed.2.2.1.symm
  have hB : wordMatrix wB = M 3 := wordMatrix_B.trans hseed.2.2.2.symm
  have hg0 : wordMatrix wg0 = M 4 :=
    (wordMatrix_append wa wb).trans
      ((congrArg₂ (· * ·) ha hb).trans (hshared 0))
  have hg1 : wordMatrix wg1 = M 5 :=
    (wordMatrix_append wa wB).trans
      ((congrArg₂ (· * ·) ha hB).trans (hshared 1))
  have hg2 : wordMatrix wg2 = M 6 :=
    (wordMatrix_append wg0 wg1).trans
      ((congrArg₂ (· * ·) hg0 hg1).trans (hshared 2))
  have hg3 : wordMatrix wg3 = M 7 :=
    (wordMatrix_append wg2 wg2).trans
      ((congrArg₂ (· * ·) hg2 hg2).trans (hshared 3))
  have hg4 : wordMatrix wg4 = M 8 :=
    (wordMatrix_append wg2 wg1).trans
      ((congrArg₂ (· * ·) hg2 hg1).trans (hshared 4))
  have hg5 : wordMatrix wg5 = M 9 :=
    (wordMatrix_append wg0 wg3).trans
      ((congrArg₂ (· * ·) hg0 hg3).trans (hshared 5))
  have hg6 : wordMatrix wg6 = M 10 :=
    (wordMatrix_append wg0 wg4).trans
      ((congrArg₂ (· * ·) hg0 hg4).trans (hshared 6))
  have hg7 : wordMatrix wg7 = M 11 :=
    (wordMatrix_append wg6 wg3).trans
      ((congrArg₂ (· * ·) hg6 hg3).trans (hshared 7))
  have hg8 : wordMatrix wg8 = M 12 :=
    (wordMatrix_append wg2 wg7).trans
      ((congrArg₂ (· * ·) hg2 hg7).trans (hshared 8))
  have hg9 : wordMatrix wg9 = M 13 :=
    (wordMatrix_append wg1 wg3).trans
      ((congrArg₂ (· * ·) hg1 hg3).trans (hshared 9))
  have hg10 : wordMatrix wg10 = M 14 :=
    (wordMatrix_append wg7 wg3).trans
      ((congrArg₂ (· * ·) hg7 hg3).trans (hshared 10))
  have hg11 : wordMatrix wg11 = M 15 :=
    (wordMatrix_append wg5 wg10).trans
      ((congrArg₂ (· * ·) hg5 hg10).trans (hshared 11))
  have hg12 : wordMatrix wg12 = M 16 :=
    (wordMatrix_append wg11 wg8).trans
      ((congrArg₂ (· * ·) hg11 hg8).trans (hshared 12))
  have hg13 : wordMatrix wg13 = M 17 :=
    (wordMatrix_append wg5 wg3).trans
      ((congrArg₂ (· * ·) hg5 hg3).trans (hshared 13))
  have hg14 : wordMatrix wg14 = M 18 :=
    (wordMatrix_append wg0 wg2).trans
      ((congrArg₂ (· * ·) hg0 hg2).trans (hshared 14))
  have hg15 : wordMatrix wg15 = M 19 :=
    (wordMatrix_append wg4 wg3).trans
      ((congrArg₂ (· * ·) hg4 hg3).trans (hshared 15))
  have hg16 : wordMatrix wg16 = M 20 :=
    (wordMatrix_append wg12 wg9).trans
      ((congrArg₂ (· * ·) hg12 hg9).trans (hshared 16))
  have hg17 : wordMatrix wg17 = M 21 :=
    (wordMatrix_append wg16 wg13).trans
      ((congrArg₂ (· * ·) hg16 hg13).trans (hshared 17))
  have hg18 : wordMatrix wg18 = M 22 :=
    (wordMatrix_append wg5 wg1).trans
      ((congrArg₂ (· * ·) hg5 hg1).trans (hshared 18))
  have hg19 : wordMatrix wg19 = M 23 :=
    (wordMatrix_append wg12 wg1).trans
      ((congrArg₂ (· * ·) hg12 hg1).trans (hshared 19))
  have hg20 : wordMatrix wg20 = M 24 :=
    (wordMatrix_append wg9 wg1).trans
      ((congrArg₂ (· * ·) hg9 hg1).trans (hshared 20))
  have hg21 : wordMatrix wg21 = M 25 :=
    (wordMatrix_append wg17 wg4).trans
      ((congrArg₂ (· * ·) hg17 hg4).trans (hshared 21))
  have hg22 : wordMatrix wg22 = M 26 :=
    (wordMatrix_append wg4 wg2).trans
      ((congrArg₂ (· * ·) hg4 hg2).trans (hshared 22))
  have hg23 : wordMatrix wg23 = M 27 :=
    (wordMatrix_append wg14 wg14).trans
      ((congrArg₂ (· * ·) hg14 hg14).trans (hshared 23))
  have hg24 : wordMatrix wg24 = M 28 :=
    (wordMatrix_append wg5 wg2).trans
      ((congrArg₂ (· * ·) hg5 hg2).trans (hshared 24))
  have hg25 : wordMatrix wg25 = M 29 :=
    (wordMatrix_append wg0 wg8).trans
      ((congrArg₂ (· * ·) hg0 hg8).trans (hshared 25))
  have hg26 : wordMatrix wg26 = M 30 :=
    (wordMatrix_append wg15 wg19).trans
      ((congrArg₂ (· * ·) hg15 hg19).trans (hshared 26))
  have hg27 : wordMatrix wg27 = M 31 :=
    (wordMatrix_append wg14 wg18).trans
      ((congrArg₂ (· * ·) hg14 hg18).trans (hshared 27))
  have hg28 : wordMatrix wg28 = M 32 :=
    (wordMatrix_append wg6 wg4).trans
      ((congrArg₂ (· * ·) hg6 hg4).trans (hshared 28))
  have hg29 : wordMatrix wg29 = M 33 :=
    (wordMatrix_append wg15 wg1).trans
      ((congrArg₂ (· * ·) hg15 hg1).trans (hshared 29))
  have hg30 : wordMatrix wg30 = M 34 :=
    (wordMatrix_append wg4 wg4).trans
      ((congrArg₂ (· * ·) hg4 hg4).trans (hshared 30))
  have hg31 : wordMatrix wg31 = M 35 :=
    (wordMatrix_append wg5 wg20).trans
      ((congrArg₂ (· * ·) hg5 hg20).trans (hshared 31))
  have hg32 : wordMatrix wg32 = M 36 :=
    (wordMatrix_append wg0 wg0).trans
      ((congrArg₂ (· * ·) hg0 hg0).trans (hshared 32))
  have hg33 : wordMatrix wg33 = M 37 :=
    (wordMatrix_append wg14 wg6).trans
      ((congrArg₂ (· * ·) hg14 hg6).trans (hshared 33))
  have hg34 : wordMatrix wg34 = M 38 :=
    (wordMatrix_append wg13 wg1).trans
      ((congrArg₂ (· * ·) hg13 hg1).trans (hshared 34))
  have hg35 : wordMatrix wg35 = M 39 :=
    (wordMatrix_append wg6 wg2).trans
      ((congrArg₂ (· * ·) hg6 hg2).trans (hshared 35))
  have hg36 : wordMatrix wg36 = M 40 :=
    (wordMatrix_append wg5 wg4).trans
      ((congrArg₂ (· * ·) hg5 hg4).trans (hshared 36))
  have hg37 : wordMatrix wg37 = M 41 :=
    (wordMatrix_append wg13 wg26).trans
      ((congrArg₂ (· * ·) hg13 hg26).trans (hshared 37))
  have hg38 : wordMatrix wg38 = M 42 :=
    (wordMatrix_append wg3 wg3).trans
      ((congrArg₂ (· * ·) hg3 hg3).trans (hshared 38))
  have hg39 : wordMatrix wg39 = M 43 :=
    (wordMatrix_append wg9 wg19).trans
      ((congrArg₂ (· * ·) hg9 hg19).trans (hshared 39))
  have hg40 : wordMatrix wg40 = M 44 :=
    (wordMatrix_append wg21 wg31).trans
      ((congrArg₂ (· * ·) hg21 hg31).trans (hshared 40))
  have hg41 : wordMatrix wg41 = M 45 :=
    (wordMatrix_append wg8 wg3).trans
      ((congrArg₂ (· * ·) hg8 hg3).trans (hshared 41))
  have hg42 : wordMatrix wg42 = M 46 :=
    (wordMatrix_append wg15 wg20).trans
      ((congrArg₂ (· * ·) hg15 hg20).trans (hshared 42))
  have hg43 : wordMatrix wg43 = M 47 :=
    (wordMatrix_append wg33 wg27).trans
      ((congrArg₂ (· * ·) hg33 hg27).trans (hshared 43))
  have hg44 : wordMatrix wg44 = M 48 :=
    (wordMatrix_append wg13 wg3).trans
      ((congrArg₂ (· * ·) hg13 hg3).trans (hshared 44))
  have hg45 : wordMatrix wg45 = M 49 :=
    (wordMatrix_append wg5 wg5).trans
      ((congrArg₂ (· * ·) hg5 hg5).trans (hshared 45))
  have hg46 : wordMatrix wg46 = M 50 :=
    (wordMatrix_append wg12 wg22).trans
      ((congrArg₂ (· * ·) hg12 hg22).trans (hshared 46))
  have hg47 : wordMatrix wg47 = M 51 :=
    (wordMatrix_append wg2 wg6).trans
      ((congrArg₂ (· * ·) hg2 hg6).trans (hshared 47))
  have hg48 : wordMatrix wg48 = M 52 :=
    (wordMatrix_append wg18 wg37).trans
      ((congrArg₂ (· * ·) hg18 hg37).trans (hshared 48))
  have hg49 : wordMatrix wg49 = M 53 :=
    (wordMatrix_append wb wg9).trans
      ((congrArg₂ (· * ·) hb hg9).trans (hshared 49))
  have hg50 : wordMatrix wg50 = M 54 :=
    (wordMatrix_append wg22 wg43).trans
      ((congrArg₂ (· * ·) hg22 hg43).trans (hshared 50))
  have hg51 : wordMatrix wg51 = M 55 :=
    (wordMatrix_append wg4 wg6).trans
      ((congrArg₂ (· * ·) hg4 hg6).trans (hshared 51))
  have hg52 : wordMatrix wg52 = M 56 :=
    (wordMatrix_append wg21 wg4).trans
      ((congrArg₂ (· * ·) hg21 hg4).trans (hshared 52))
  have hg53 : wordMatrix wg53 = M 57 :=
    (wordMatrix_append wg5 wg14).trans
      ((congrArg₂ (· * ·) hg5 hg14).trans (hshared 53))
  have hg54 : wordMatrix wg54 = M 58 :=
    (wordMatrix_append wg1 wg5).trans
      ((congrArg₂ (· * ·) hg1 hg5).trans (hshared 54))
  have hg55 : wordMatrix wg55 = M 59 :=
    (wordMatrix_append wg8 wg9).trans
      ((congrArg₂ (· * ·) hg8 hg9).trans (hshared 55))
  have hg56 : wordMatrix wg56 = M 60 :=
    (wordMatrix_append wg14 wg5).trans
      ((congrArg₂ (· * ·) hg14 hg5).trans (hshared 56))
  have hg57 : wordMatrix wg57 = M 61 :=
    (wordMatrix_append wg1 wg2).trans
      ((congrArg₂ (· * ·) hg1 hg2).trans (hshared 57))
  have hg58 : wordMatrix wg58 = M 62 :=
    (wordMatrix_append wg9 wg46).trans
      ((congrArg₂ (· * ·) hg9 hg46).trans (hshared 58))
  have hg59 : wordMatrix wg59 = M 63 :=
    (wordMatrix_append wg5 wg19).trans
      ((congrArg₂ (· * ·) hg5 hg19).trans (hshared 59))
  have hg60 : wordMatrix wg60 = M 64 :=
    (wordMatrix_append wg3 wg20).trans
      ((congrArg₂ (· * ·) hg3 hg20).trans (hshared 60))
  have hg61 : wordMatrix wg61 = M 65 :=
    (wordMatrix_append wg41 wg26).trans
      ((congrArg₂ (· * ·) hg41 hg26).trans (hshared 61))
  have hg62 : wordMatrix wg62 = M 66 :=
    (wordMatrix_append wg5 wg7).trans
      ((congrArg₂ (· * ·) hg5 hg7).trans (hshared 62))
  have hg63 : wordMatrix wg63 = M 67 :=
    (wordMatrix_append wg62 wg30).trans
      ((congrArg₂ (· * ·) hg62 hg30).trans (hshared 63))
  have hg64 : wordMatrix wg64 = M 68 :=
    (wordMatrix_append wg63 wg16).trans
      ((congrArg₂ (· * ·) hg63 hg16).trans (hshared 64))
  have hg65 : wordMatrix wg65 = M 69 :=
    (wordMatrix_append wg6 wg35).trans
      ((congrArg₂ (· * ·) hg6 hg35).trans (hshared 65))
  have hg66 : wordMatrix wg66 = M 70 :=
    (wordMatrix_append wg21 wg48).trans
      ((congrArg₂ (· * ·) hg21 hg48).trans (hshared 66))
  have hg67 : wordMatrix wg67 = M 71 :=
    (wordMatrix_append wg36 wg28).trans
      ((congrArg₂ (· * ·) hg36 hg28).trans (hshared 67))
  have hg68 : wordMatrix wg68 = M 72 :=
    (wordMatrix_append wg67 wg29).trans
      ((congrArg₂ (· * ·) hg67 hg29).trans (hshared 68))
  have hg69 : wordMatrix wg69 = M 73 :=
    (wordMatrix_append wg68 wg30).trans
      ((congrArg₂ (· * ·) hg68 hg30).trans (hshared 69))
  have hg70 : wordMatrix wg70 = M 3 :=
    (wordMatrix_append wb wb).trans
      ((congrArg₂ (· * ·) hb hb).trans (hshared 70))
  have hg71 : wordMatrix wg71 = M 74 :=
    (wordMatrix_append wg32 wg32).trans
      ((congrArg₂ (· * ·) hg32 hg32).trans (hshared 71))
  have hg72 : wordMatrix wg72 = M 75 :=
    (wordMatrix_append wg38 wg38).trans
      ((congrArg₂ (· * ·) hg38 hg38).trans (hshared 72))
  have hg73 : wordMatrix wg73 = M 76 :=
    (wordMatrix_append wg24 wg5).trans
      ((congrArg₂ (· * ·) hg24 hg5).trans (hshared 73))
  have hg74 : wordMatrix wg74 = M 77 :=
    (wordMatrix_append wg73 wg24).trans
      ((congrArg₂ (· * ·) hg73 hg24).trans (hshared 74))
  have hg75 : wordMatrix wg75 = M 78 :=
    (wordMatrix_append wg27 wg50).trans
      ((congrArg₂ (· * ·) hg27 hg50).trans (hshared 75))
  have hg76 : wordMatrix wg76 = M 79 :=
    (wordMatrix_append wg51 wg22).trans
      ((congrArg₂ (· * ·) hg51 hg22).trans (hshared 76))
  have hg77 : wordMatrix wg77 = M 80 :=
    (wordMatrix_append wg2 wg14).trans
      ((congrArg₂ (· * ·) hg2 hg14).trans (hshared 77))
  have hg78 : wordMatrix wg78 = M 81 :=
    (wordMatrix_append wg21 wg23).trans
      ((congrArg₂ (· * ·) hg21 hg23).trans (hshared 78))
  have hg79 : wordMatrix wg79 = M 82 :=
    (wordMatrix_append wg44 wg39).trans
      ((congrArg₂ (· * ·) hg44 hg39).trans (hshared 79))
  have hg80 : wordMatrix wg80 = M 83 :=
    (wordMatrix_append wg25 wg54).trans
      ((congrArg₂ (· * ·) hg25 hg54).trans (hshared 80))
  have hg81 : wordMatrix wg81 = M 84 :=
    (wordMatrix_append wg29 wg52).trans
      ((congrArg₂ (· * ·) hg29 hg52).trans (hshared 81))
  have hg82 : wordMatrix wg82 = M 85 :=
    (wordMatrix_append wg1 wg4).trans
      ((congrArg₂ (· * ·) hg1 hg4).trans (hshared 82))
  have hg83 : wordMatrix wg83 = M 86 :=
    (wordMatrix_append wg13 wg39).trans
      ((congrArg₂ (· * ·) hg13 hg39).trans (hshared 83))
  have hg84 : wordMatrix wg84 = M 87 :=
    (wordMatrix_append wg53 wa).trans
      ((congrArg₂ (· * ·) hg53 ha).trans (hshared 84))
  have hg85 : wordMatrix wg85 = M 88 :=
    (wordMatrix_append wg28 wg17).trans
      ((congrArg₂ (· * ·) hg28 hg17).trans (hshared 85))
  have hg86 : wordMatrix wg86 = M 89 :=
    (wordMatrix_append wg18 wg2).trans
      ((congrArg₂ (· * ·) hg18 hg2).trans (hshared 86))
  have hg87 : wordMatrix wg87 = M 90 :=
    (wordMatrix_append wg19 wg4).trans
      ((congrArg₂ (· * ·) hg19 hg4).trans (hshared 87))
  have hg88 : wordMatrix wg88 = M 91 :=
    (wordMatrix_append wg87 wg10).trans
      ((congrArg₂ (· * ·) hg87 hg10).trans (hshared 88))
  have hg89 : wordMatrix wg89 = M 92 :=
    (wordMatrix_append wg88 wg57).trans
      ((congrArg₂ (· * ·) hg88 hg57).trans (hshared 89))
  have hg90 : wordMatrix wg90 = M 93 :=
    (wordMatrix_append wg24 wg23).trans
      ((congrArg₂ (· * ·) hg24 hg23).trans (hshared 90))
  have hg91 : wordMatrix wg91 = M 94 :=
    (wordMatrix_append wg90 wg45).trans
      ((congrArg₂ (· * ·) hg90 hg45).trans (hshared 91))
  have hg92 : wordMatrix wg92 = M 95 :=
    (wordMatrix_append wg23 wg56).trans
      ((congrArg₂ (· * ·) hg23 hg56).trans (hshared 92))
  have hg93 : wordMatrix wg93 = M 96 :=
    (wordMatrix_append wg92 wg23).trans
      ((congrArg₂ (· * ·) hg92 hg23).trans (hshared 93))
  have hg94 : wordMatrix wg94 = M 97 :=
    (wordMatrix_append wg93 wg6).trans
      ((congrArg₂ (· * ·) hg93 hg6).trans (hshared 94))
  have hg95 : wordMatrix wg95 = M 98 :=
    (wordMatrix_append wg5 wg35).trans
      ((congrArg₂ (· * ·) hg5 hg35).trans (hshared 95))
  have hg96 : wordMatrix wg96 = M 99 :=
    (wordMatrix_append wg95 wg18).trans
      ((congrArg₂ (· * ·) hg95 hg18).trans (hshared 96))
  have hg97 : wordMatrix wg97 = M 100 :=
    (wordMatrix_append wg96 wg22).trans
      ((congrArg₂ (· * ·) hg96 hg22).trans (hshared 97))
  have hg98 : wordMatrix wg98 = M 101 :=
    (wordMatrix_append wg97 wg13).trans
      ((congrArg₂ (· * ·) hg97 hg13).trans (hshared 98))
  have hg99 : wordMatrix wg99 = M 102 :=
    (wordMatrix_append wg98 wg58).trans
      ((congrArg₂ (· * ·) hg98 hg58).trans (hshared 99))
  have hg100 : wordMatrix wg100 = M 103 :=
    (wordMatrix_append wg59 wg25).trans
      ((congrArg₂ (· * ·) hg59 hg25).trans (hshared 100))
  have hg101 : wordMatrix wg101 = M 104 :=
    (wordMatrix_append wg60 wg17).trans
      ((congrArg₂ (· * ·) hg60 hg17).trans (hshared 101))
  have hg102 : wordMatrix wg102 = M 105 :=
    (wordMatrix_append wg33 wg0).trans
      ((congrArg₂ (· * ·) hg33 hg0).trans (hshared 102))
  have hg103 : wordMatrix wg103 = M 106 :=
    (wordMatrix_append wg5 wg41).trans
      ((congrArg₂ (· * ·) hg5 hg41).trans (hshared 103))
  have hg104 : wordMatrix wg104 = M 107 :=
    (wordMatrix_append wg103 wg55).trans
      ((congrArg₂ (· * ·) hg103 hg55).trans (hshared 104))
  have hg105 : wordMatrix wg105 = M 108 :=
    (wordMatrix_append wg5 wg65).trans
      ((congrArg₂ (· * ·) hg5 hg65).trans (hshared 105))
  have hg106 : wordMatrix wg106 = M 109 :=
    (wordMatrix_append wg105 wg5).trans
      ((congrArg₂ (· * ·) hg105 hg5).trans (hshared 106))
  have hg107 : wordMatrix wg107 = M 110 :=
    (wordMatrix_append wg106 wg25).trans
      ((congrArg₂ (· * ·) hg106 hg25).trans (hshared 107))
  have hg108 : wordMatrix wg108 = M 111 :=
    (wordMatrix_append wg107 wg2).trans
      ((congrArg₂ (· * ·) hg107 hg2).trans (hshared 108))
  have hg109 : wordMatrix wg109 = M 112 :=
    (wordMatrix_append wg108 wg64).trans
      ((congrArg₂ (· * ·) hg108 hg64).trans (hshared 109))
  have hg110 : wordMatrix wg110 = M 113 :=
    (wordMatrix_append wg109 wg6).trans
      ((congrArg₂ (· * ·) hg109 hg6).trans (hshared 110))
  have hg111 : wordMatrix wg111 = M 114 :=
    (wordMatrix_append wg5 wg31).trans
      ((congrArg₂ (· * ·) hg5 hg31).trans (hshared 111))
  have hg112 : wordMatrix wg112 = M 115 :=
    (wordMatrix_append wg69 wg15).trans
      ((congrArg₂ (· * ·) hg69 hg15).trans (hshared 112))
  have hr0p0 : wordMatrix wr0p0 = M 0 :=
    (wordMatrix_append wa wa).trans
      ((congrArg₂ (· * ·) ha ha).trans (hfirst 0))
  have hr1p0 : wordMatrix wr1p0 = M 0 :=
    (wordMatrix_append wg70 wb).trans
      ((congrArg₂ (· * ·) hg70 hb).trans (hfirst 1))
  have hr2p0 : wordMatrix wr2p0 = M 116 :=
    (wordMatrix_append wg71 wg32).trans
      ((congrArg₂ (· * ·) hg71 hg32).trans (hfirst 2))
  have hr2p1 : wordMatrix wr2p1 = M 0 :=
    (wordMatrix_append wr2p0 wg0).trans
      ((congrArg₂ (· * ·) hr2p0 hg0).trans (hfirst 3))
  have hr3p0 : wordMatrix wr3p0 = M 117 :=
    (wordMatrix_append wg49 wg72).trans
      ((congrArg₂ (· * ·) hg49 hg72).trans (hfirst 4))
  have hr3p1 : wordMatrix wr3p1 = M 1 :=
    (wordMatrix_append wr3p0 wg38).trans
      ((congrArg₂ (· * ·) hr3p0 hg38).trans (hfirst 5))
  have hr3p2 : wordMatrix wr3p2 = M 0 :=
    (wordMatrix_append wr3p1 wa).trans
      ((congrArg₂ (· * ·) hr3p1 ha).trans (hfirst 6))
  have hr4p0 : wordMatrix wr4p0 = M 118 :=
    (wordMatrix_append wg49 wg2).trans
      ((congrArg₂ (· * ·) hg49 hg2).trans (hfirst 7))
  have hr4p1 : wordMatrix wr4p1 = M 119 :=
    (wordMatrix_append wr4p0 wg74).trans
      ((congrArg₂ (· * ·) hr4p0 hg74).trans (hfirst 8))
  have hr4p2 : wordMatrix wr4p2 = M 120 :=
    (wordMatrix_append wr4p1 wg25).trans
      ((congrArg₂ (· * ·) hr4p1 hg25).trans (hfirst 9))
  have hr4p3 : wordMatrix wr4p3 = M 121 :=
    (wordMatrix_append wr4p2 wg15).trans
      ((congrArg₂ (· * ·) hr4p2 hg15).trans (hfirst 10))
  have hr4p4 : wordMatrix wr4p4 = M 122 :=
    (wordMatrix_append wr4p3 wg42).trans
      ((congrArg₂ (· * ·) hr4p3 hg42).trans (hfirst 11))
  have hr4p5 : wordMatrix wr4p5 = M 123 :=
    (wordMatrix_append wr4p4 wg14).trans
      ((congrArg₂ (· * ·) hr4p4 hg14).trans (hfirst 12))
  have hr4p6 : wordMatrix wr4p6 = M 1 :=
    (wordMatrix_append wr4p5 wg0).trans
      ((congrArg₂ (· * ·) hr4p5 hg0).trans (hfirst 13))
  have hr4p7 : wordMatrix wr4p7 = M 0 :=
    (wordMatrix_append wr4p6 wa).trans
      ((congrArg₂ (· * ·) hr4p6 ha).trans (hfirst 14))
  have hr5p0 : wordMatrix wr5p0 = M 124 :=
    (wordMatrix_append wg75 wg76).trans
      ((congrArg₂ (· * ·) hg75 hg76).trans (hfirst 15))
  have hr5p1 : wordMatrix wr5p1 = M 125 :=
    (wordMatrix_append wr5p0 wg75).trans
      ((congrArg₂ (· * ·) hr5p0 hg75).trans (hfirst 16))
  have hr5p2 : wordMatrix wr5p2 = M 126 :=
    (wordMatrix_append wr5p1 wg50).trans
      ((congrArg₂ (· * ·) hr5p1 hg50).trans (hfirst 17))
  have hr5p3 : wordMatrix wr5p3 = M 0 :=
    (wordMatrix_append wr5p2 wg76).trans
      ((congrArg₂ (· * ·) hr5p2 hg76).trans (hfirst 18))
  have hr6p0 : wordMatrix wr6p0 = M 127 :=
    (wordMatrix_append wg77 wg34).trans
      ((congrArg₂ (· * ·) hg77 hg34).trans (hfirst 19))
  have hr6p1 : wordMatrix wr6p1 = M 128 :=
    (wordMatrix_append wr6p0 wg16).trans
      ((congrArg₂ (· * ·) hr6p0 hg16).trans (hfirst 20))
  have hr6p2 : wordMatrix wr6p2 = M 129 :=
    (wordMatrix_append wr6p1 wg24).trans
      ((congrArg₂ (· * ·) hr6p1 hg24).trans (hfirst 21))
  have hr6p3 : wordMatrix wr6p3 = M 130 :=
    (wordMatrix_append wr6p2 wg35).trans
      ((congrArg₂ (· * ·) hr6p2 hg35).trans (hfirst 22))
  have hr6p4 : wordMatrix wr6p4 = M 131 :=
    (wordMatrix_append wr6p3 wg52).trans
      ((congrArg₂ (· * ·) hr6p3 hg52).trans (hfirst 23))
  have hr6p5 : wordMatrix wr6p5 = M 0 :=
    (wordMatrix_append wr6p4 wg53).trans
      ((congrArg₂ (· * ·) hr6p4 hg53).trans (hfirst 24))
  have hr7p0 : wordMatrix wr7p0 = M 132 :=
    (wordMatrix_append wg28 wg78).trans
      ((congrArg₂ (· * ·) hg28 hg78).trans (hfirst 25))
  have hr7p1 : wordMatrix wr7p1 = M 133 :=
    (wordMatrix_append wr7p0 wg24).trans
      ((congrArg₂ (· * ·) hr7p0 hg24).trans (hfirst 26))
  have hr7p2 : wordMatrix wr7p2 = M 134 :=
    (wordMatrix_append wr7p1 wg79).trans
      ((congrArg₂ (· * ·) hr7p1 hg79).trans (hfirst 27))
  have hr7p3 : wordMatrix wr7p3 = M 0 :=
    (wordMatrix_append wr7p2 wg80).trans
      ((congrArg₂ (· * ·) hr7p2 hg80).trans (hfirst 28))
  have hr8p0 : wordMatrix wr8p0 = M 135 :=
    (wordMatrix_append wg49 wg81).trans
      ((congrArg₂ (· * ·) hg49 hg81).trans (hfirst 29))
  have hr8p1 : wordMatrix wr8p1 = M 136 :=
    (wordMatrix_append wr8p0 wg43).trans
      ((congrArg₂ (· * ·) hr8p0 hg43).trans (hfirst 30))
  have hr8p2 : wordMatrix wr8p2 = M 137 :=
    (wordMatrix_append wr8p1 wg4).trans
      ((congrArg₂ (· * ·) hr8p1 hg4).trans (hfirst 31))
  have hr8p3 : wordMatrix wr8p3 = M 138 :=
    (wordMatrix_append wr8p2 wg7).trans
      ((congrArg₂ (· * ·) hr8p2 hg7).trans (hfirst 32))
  have hr8p4 : wordMatrix wr8p4 = M 139 :=
    (wordMatrix_append wr8p3 wg82).trans
      ((congrArg₂ (· * ·) hr8p3 hg82).trans (hfirst 33))
  have hr8p5 : wordMatrix wr8p5 = M 140 :=
    (wordMatrix_append wr8p4 wg83).trans
      ((congrArg₂ (· * ·) hr8p4 hg83).trans (hfirst 34))
  have hr8p6 : wordMatrix wr8p6 = M 0 :=
    (wordMatrix_append wr8p5 wg84).trans
      ((congrArg₂ (· * ·) hr8p5 hg84).trans (hfirst 35))
  have hr9p0 : wordMatrix wr9p0 = M 141 :=
    (wordMatrix_append wg74 wg85).trans
      ((congrArg₂ (· * ·) hg74 hg85).trans (hfirst 36))
  have hr9p1 : wordMatrix wr9p1 = M 142 :=
    (wordMatrix_append wr9p0 wg42).trans
      ((congrArg₂ (· * ·) hr9p0 hg42).trans (hfirst 37))
  have hr9p2 : wordMatrix wr9p2 = M 143 :=
    (wordMatrix_append wr9p1 wg5).trans
      ((congrArg₂ (· * ·) hr9p1 hg5).trans (hfirst 38))
  have hr9p3 : wordMatrix wr9p3 = M 144 :=
    (wordMatrix_append wr9p2 wg55).trans
      ((congrArg₂ (· * ·) hr9p2 hg55).trans (hfirst 39))
  have hr9p4 : wordMatrix wr9p4 = M 145 :=
    (wordMatrix_append wr9p3 wg20).trans
      ((congrArg₂ (· * ·) hr9p3 hg20).trans (hfirst 40))
  have hr9p5 : wordMatrix wr9p5 = M 146 :=
    (wordMatrix_append wr9p4 wg4).trans
      ((congrArg₂ (· * ·) hr9p4 hg4).trans (hfirst 41))
  have hr9p6 : wordMatrix wr9p6 = M 147 :=
    (wordMatrix_append wr9p5 wg81).trans
      ((congrArg₂ (· * ·) hr9p5 hg81).trans (hfirst 42))
  have hr9p7 : wordMatrix wr9p7 = M 0 :=
    (wordMatrix_append wr9p6 wg56).trans
      ((congrArg₂ (· * ·) hr9p6 hg56).trans (hfirst 43))
  have hr10p0 : wordMatrix wr10p0 = M 148 :=
    (wordMatrix_append wg3 wg4).trans
      ((congrArg₂ (· * ·) hg3 hg4).trans (hfirst 44))
  have hr10p1 : wordMatrix wr10p1 = M 149 :=
    (wordMatrix_append wr10p0 wg86).trans
      ((congrArg₂ (· * ·) hr10p0 hg86).trans (hfirst 45))
  have hr10p2 : wordMatrix wr10p2 = M 150 :=
    (wordMatrix_append wr10p1 wg28).trans
      ((congrArg₂ (· * ·) hr10p1 hg28).trans (hfirst 46))
  have hr10p3 : wordMatrix wr10p3 = M 151 :=
    (wordMatrix_append wr10p2 wg89).trans
      ((congrArg₂ (· * ·) hr10p2 hg89).trans (hfirst 47))
  have hr10p4 : wordMatrix wr10p4 = M 152 :=
    (wordMatrix_append wr10p3 wg91).trans
      ((congrArg₂ (· * ·) hr10p3 hg91).trans (hfirst 48))
  have hr10p5 : wordMatrix wr10p5 = M 153 :=
    (wordMatrix_append wr10p4 wg13).trans
      ((congrArg₂ (· * ·) hr10p4 hg13).trans (hfirst 49))
  have hr10p6 : wordMatrix wr10p6 = M 154 :=
    (wordMatrix_append wr10p5 wg79).trans
      ((congrArg₂ (· * ·) hr10p5 hg79).trans (hfirst 50))
  have hr10p7 : wordMatrix wr10p7 = M 155 :=
    (wordMatrix_append wr10p6 wg6).trans
      ((congrArg₂ (· * ·) hr10p6 hg6).trans (hfirst 51))
  have hr10p8 : wordMatrix wr10p8 = M 156 :=
    (wordMatrix_append wr10p7 wg6).trans
      ((congrArg₂ (· * ·) hr10p7 hg6).trans (hfirst 52))
  have hr10p9 : wordMatrix wr10p9 = M 116 :=
    (wordMatrix_append wr10p8 wg94).trans
      ((congrArg₂ (· * ·) hr10p8 hg94).trans (hfirst 53))
  have hr10p10 : wordMatrix wr10p10 = M 0 :=
    (wordMatrix_append wr10p9 wg0).trans
      ((congrArg₂ (· * ·) hr10p9 hg0).trans (hfirst 54))
  have hr11p0 : wordMatrix wr11p0 = M 157 :=
    (wordMatrix_append wg91 wg5).trans
      ((congrArg₂ (· * ·) hg91 hg5).trans (hlast 0))
  have hr11p1 : wordMatrix wr11p1 = M 158 :=
    (wordMatrix_append wr11p0 wg34).trans
      ((congrArg₂ (· * ·) hr11p0 hg34).trans (hlast 1))
  have hr11p2 : wordMatrix wr11p2 = M 159 :=
    (wordMatrix_append wr11p1 wg17).trans
      ((congrArg₂ (· * ·) hr11p1 hg17).trans (hlast 2))
  have hr11p3 : wordMatrix wr11p3 = M 160 :=
    (wordMatrix_append wr11p2 wg1).trans
      ((congrArg₂ (· * ·) hr11p2 hg1).trans (hlast 3))
  have hr11p4 : wordMatrix wr11p4 = M 161 :=
    (wordMatrix_append wr11p3 wg14).trans
      ((congrArg₂ (· * ·) hr11p3 hg14).trans (hlast 4))
  have hr11p5 : wordMatrix wr11p5 = M 162 :=
    (wordMatrix_append wr11p4 wg13).trans
      ((congrArg₂ (· * ·) hr11p4 hg13).trans (hlast 5))
  have hr11p6 : wordMatrix wr11p6 = M 163 :=
    (wordMatrix_append wr11p5 wg28).trans
      ((congrArg₂ (· * ·) hr11p5 hg28).trans (hlast 6))
  have hr11p7 : wordMatrix wr11p7 = M 164 :=
    (wordMatrix_append wr11p6 wg40).trans
      ((congrArg₂ (· * ·) hr11p6 hg40).trans (hlast 7))
  have hr11p8 : wordMatrix wr11p8 = M 0 :=
    (wordMatrix_append wr11p7 wg89).trans
      ((congrArg₂ (· * ·) hr11p7 hg89).trans (hlast 8))
  have hr12p0 : wordMatrix wr12p0 = M 165 :=
    (wordMatrix_append wg3 wg19).trans
      ((congrArg₂ (· * ·) hg3 hg19).trans (hlast 9))
  have hr12p1 : wordMatrix wr12p1 = M 166 :=
    (wordMatrix_append wr12p0 wg99).trans
      ((congrArg₂ (· * ·) hr12p0 hg99).trans (hlast 10))
  have hr12p2 : wordMatrix wr12p2 = M 167 :=
    (wordMatrix_append wr12p1 wg59).trans
      ((congrArg₂ (· * ·) hr12p1 hg59).trans (hlast 11))
  have hr12p3 : wordMatrix wr12p3 = M 116 :=
    (wordMatrix_append wr12p2 wg99).trans
      ((congrArg₂ (· * ·) hr12p2 hg99).trans (hlast 12))
  have hr12p4 : wordMatrix wr12p4 = M 0 :=
    (wordMatrix_append wr12p3 wg0).trans
      ((congrArg₂ (· * ·) hr12p3 hg0).trans (hlast 13))
  have hr13p0 : wordMatrix wr13p0 = M 168 :=
    (wordMatrix_append wg44 wg58).trans
      ((congrArg₂ (· * ·) hg44 hg58).trans (hlast 14))
  have hr13p1 : wordMatrix wr13p1 = M 169 :=
    (wordMatrix_append wr13p0 wg100).trans
      ((congrArg₂ (· * ·) hr13p0 hg100).trans (hlast 15))
  have hr13p2 : wordMatrix wr13p2 = M 170 :=
    (wordMatrix_append wr13p1 wg42).trans
      ((congrArg₂ (· * ·) hr13p1 hg42).trans (hlast 16))
  have hr13p3 : wordMatrix wr13p3 = M 171 :=
    (wordMatrix_append wr13p2 wg30).trans
      ((congrArg₂ (· * ·) hr13p2 hg30).trans (hlast 17))
  have hr13p4 : wordMatrix wr13p4 = M 172 :=
    (wordMatrix_append wr13p3 wg13).trans
      ((congrArg₂ (· * ·) hr13p3 hg13).trans (hlast 18))
  have hr13p5 : wordMatrix wr13p5 = M 173 :=
    (wordMatrix_append wr13p4 wg15).trans
      ((congrArg₂ (· * ·) hr13p4 hg15).trans (hlast 19))
  have hr13p6 : wordMatrix wr13p6 = M 174 :=
    (wordMatrix_append wr13p5 wg46).trans
      ((congrArg₂ (· * ·) hr13p5 hg46).trans (hlast 20))
  have hr13p7 : wordMatrix wr13p7 = M 175 :=
    (wordMatrix_append wr13p6 wg100).trans
      ((congrArg₂ (· * ·) hr13p6 hg100).trans (hlast 21))
  have hr13p8 : wordMatrix wr13p8 = M 176 :=
    (wordMatrix_append wr13p7 wg3).trans
      ((congrArg₂ (· * ·) hr13p7 hg3).trans (hlast 22))
  have hr13p9 : wordMatrix wr13p9 = M 177 :=
    (wordMatrix_append wr13p8 wg82).trans
      ((congrArg₂ (· * ·) hr13p8 hg82).trans (hlast 23))
  have hr13p10 : wordMatrix wr13p10 = M 0 :=
    (wordMatrix_append wr13p9 wg24).trans
      ((congrArg₂ (· * ·) hr13p9 hg24).trans (hlast 24))
  have hr14p0 : wordMatrix wr14p0 = M 178 :=
    (wordMatrix_append wg9 wg101).trans
      ((congrArg₂ (· * ·) hg9 hg101).trans (hlast 25))
  have hr14p1 : wordMatrix wr14p1 = M 179 :=
    (wordMatrix_append wr14p0 wg47).trans
      ((congrArg₂ (· * ·) hr14p0 hg47).trans (hlast 26))
  have hr14p2 : wordMatrix wr14p2 = M 180 :=
    (wordMatrix_append wr14p1 wg61).trans
      ((congrArg₂ (· * ·) hr14p1 hg61).trans (hlast 27))
  have hr14p3 : wordMatrix wr14p3 = M 181 :=
    (wordMatrix_append wr14p2 wg6).trans
      ((congrArg₂ (· * ·) hr14p2 hg6).trans (hlast 28))
  have hr14p4 : wordMatrix wr14p4 = M 182 :=
    (wordMatrix_append wr14p3 wg10).trans
      ((congrArg₂ (· * ·) hr14p3 hg10).trans (hlast 29))
  have hr14p5 : wordMatrix wr14p5 = M 183 :=
    (wordMatrix_append wr14p4 wg54).trans
      ((congrArg₂ (· * ·) hr14p4 hg54).trans (hlast 30))
  have hr14p6 : wordMatrix wr14p6 = M 184 :=
    (wordMatrix_append wr14p5 wg8).trans
      ((congrArg₂ (· * ·) hr14p5 hg8).trans (hlast 31))
  have hr14p7 : wordMatrix wr14p7 = M 185 :=
    (wordMatrix_append wr14p6 wg94).trans
      ((congrArg₂ (· * ·) hr14p6 hg94).trans (hlast 32))
  have hr14p8 : wordMatrix wr14p8 = M 186 :=
    (wordMatrix_append wr14p7 wg36).trans
      ((congrArg₂ (· * ·) hr14p7 hg36).trans (hlast 33))
  have hr14p9 : wordMatrix wr14p9 = M 187 :=
    (wordMatrix_append wr14p8 wg86).trans
      ((congrArg₂ (· * ·) hr14p8 hg86).trans (hlast 34))
  have hr14p10 : wordMatrix wr14p10 = M 188 :=
    (wordMatrix_append wr14p9 wg85).trans
      ((congrArg₂ (· * ·) hr14p9 hg85).trans (hlast 35))
  have hr14p11 : wordMatrix wr14p11 = M 0 :=
    (wordMatrix_append wr14p10 wg57).trans
      ((congrArg₂ (· * ·) hr14p10 hg57).trans (hlast 36))
  have hr15p0 : wordMatrix wr15p0 = M 189 :=
    (wordMatrix_append wg9 wg64).trans
      ((congrArg₂ (· * ·) hg9 hg64).trans (hlast 37))
  have hr15p1 : wordMatrix wr15p1 = M 190 :=
    (wordMatrix_append wr15p0 wg18).trans
      ((congrArg₂ (· * ·) hr15p0 hg18).trans (hlast 38))
  have hr15p2 : wordMatrix wr15p2 = M 191 :=
    (wordMatrix_append wr15p1 wg47).trans
      ((congrArg₂ (· * ·) hr15p1 hg47).trans (hlast 39))
  have hr15p3 : wordMatrix wr15p3 = M 192 :=
    (wordMatrix_append wr15p2 wg40).trans
      ((congrArg₂ (· * ·) hr15p2 hg40).trans (hlast 40))
  have hr15p4 : wordMatrix wr15p4 = M 193 :=
    (wordMatrix_append wr15p3 wg40).trans
      ((congrArg₂ (· * ·) hr15p3 hg40).trans (hlast 41))
  have hr15p5 : wordMatrix wr15p5 = M 194 :=
    (wordMatrix_append wr15p4 wg78).trans
      ((congrArg₂ (· * ·) hr15p4 hg78).trans (hlast 42))
  have hr15p6 : wordMatrix wr15p6 = M 0 :=
    (wordMatrix_append wr15p5 wg102).trans
      ((congrArg₂ (· * ·) hr15p5 hg102).trans (hlast 43))
  have hr16p0 : wordMatrix wr16p0 = M 195 :=
    (wordMatrix_append wg60 wg21).trans
      ((congrArg₂ (· * ·) hg60 hg21).trans (hlast 44))
  have hr16p1 : wordMatrix wr16p1 = M 196 :=
    (wordMatrix_append wr16p0 wg6).trans
      ((congrArg₂ (· * ·) hr16p0 hg6).trans (hlast 45))
  have hr16p2 : wordMatrix wr16p2 = M 197 :=
    (wordMatrix_append wr16p1 wg8).trans
      ((congrArg₂ (· * ·) hr16p1 hg8).trans (hlast 46))
  have hr16p3 : wordMatrix wr16p3 = M 198 :=
    (wordMatrix_append wr16p2 wg104).trans
      ((congrArg₂ (· * ·) hr16p2 hg104).trans (hlast 47))
  have hr16p4 : wordMatrix wr16p4 = M 199 :=
    (wordMatrix_append wr16p3 wg13).trans
      ((congrArg₂ (· * ·) hr16p3 hg13).trans (hlast 48))
  have hr16p5 : wordMatrix wr16p5 = M 200 :=
    (wordMatrix_append wr16p4 wg47).trans
      ((congrArg₂ (· * ·) hr16p4 hg47).trans (hlast 49))
  have hr16p6 : wordMatrix wr16p6 = M 201 :=
    (wordMatrix_append wr16p5 wg65).trans
      ((congrArg₂ (· * ·) hr16p5 hg65).trans (hlast 50))
  have hr16p7 : wordMatrix wr16p7 = M 202 :=
    (wordMatrix_append wr16p6 wg6).trans
      ((congrArg₂ (· * ·) hr16p6 hg6).trans (hlast 51))
  have hr16p8 : wordMatrix wr16p8 = M 203 :=
    (wordMatrix_append wr16p7 wg66).trans
      ((congrArg₂ (· * ·) hr16p7 hg66).trans (hlast 52))
  have hr16p9 : wordMatrix wr16p9 = M 204 :=
    (wordMatrix_append wr16p8 wg13).trans
      ((congrArg₂ (· * ·) hr16p8 hg13).trans (hlast 53))
  have hr16p10 : wordMatrix wr16p10 = M 116 :=
    (wordMatrix_append wr16p9 wg20).trans
      ((congrArg₂ (· * ·) hr16p9 hg20).trans (hlast 54))
  have hr16p11 : wordMatrix wr16p11 = M 0 :=
    (wordMatrix_append wr16p10 wg0).trans
      ((congrArg₂ (· * ·) hr16p10 hg0).trans (hlast 55))
  have hr17p0 : wordMatrix wr17p0 = M 205 :=
    (wordMatrix_append wg1 wg18).trans
      ((congrArg₂ (· * ·) hg1 hg18).trans (hlast 56))
  have hr17p1 : wordMatrix wr17p1 = M 206 :=
    (wordMatrix_append wr17p0 wg5).trans
      ((congrArg₂ (· * ·) hr17p0 hg5).trans (hlast 57))
  have hr17p2 : wordMatrix wr17p2 = M 207 :=
    (wordMatrix_append wr17p1 wg22).trans
      ((congrArg₂ (· * ·) hr17p1 hg22).trans (hlast 58))
  have hr17p3 : wordMatrix wr17p3 = M 208 :=
    (wordMatrix_append wr17p2 wg25).trans
      ((congrArg₂ (· * ·) hr17p2 hg25).trans (hlast 59))
  have hr17p4 : wordMatrix wr17p4 = M 209 :=
    (wordMatrix_append wr17p3 wg104).trans
      ((congrArg₂ (· * ·) hr17p3 hg104).trans (hlast 60))
  have hr17p5 : wordMatrix wr17p5 = M 210 :=
    (wordMatrix_append wr17p4 wg34).trans
      ((congrArg₂ (· * ·) hr17p4 hg34).trans (hlast 61))
  have hr17p6 : wordMatrix wr17p6 = M 211 :=
    (wordMatrix_append wr17p5 wg2).trans
      ((congrArg₂ (· * ·) hr17p5 hg2).trans (hlast 62))
  have hr17p7 : wordMatrix wr17p7 = M 212 :=
    (wordMatrix_append wr17p6 wg27).trans
      ((congrArg₂ (· * ·) hr17p6 hg27).trans (hlast 63))
  have hr17p8 : wordMatrix wr17p8 = M 213 :=
    (wordMatrix_append wr17p7 wg4).trans
      ((congrArg₂ (· * ·) hr17p7 hg4).trans (hlast 64))
  have hr17p9 : wordMatrix wr17p9 = M 214 :=
    (wordMatrix_append wr17p8 wg36).trans
      ((congrArg₂ (· * ·) hr17p8 hg36).trans (hlast 65))
  have hr17p10 : wordMatrix wr17p10 = M 215 :=
    (wordMatrix_append wr17p9 wg69).trans
      ((congrArg₂ (· * ·) hr17p9 hg69).trans (hlast 66))
  have hr17p11 : wordMatrix wr17p11 = M 216 :=
    (wordMatrix_append wr17p10 wg51).trans
      ((congrArg₂ (· * ·) hr17p10 hg51).trans (hlast 67))
  have hr17p12 : wordMatrix wr17p12 = M 217 :=
    (wordMatrix_append wr17p11 wg6).trans
      ((congrArg₂ (· * ·) hr17p11 hg6).trans (hlast 68))
  have hr17p13 : wordMatrix wr17p13 = M 218 :=
    (wordMatrix_append wr17p12 wg17).trans
      ((congrArg₂ (· * ·) hr17p12 hg17).trans (hlast 69))
  have hr17p14 : wordMatrix wr17p14 = M 219 :=
    (wordMatrix_append wr17p13 wg42).trans
      ((congrArg₂ (· * ·) hr17p13 hg42).trans (hlast 70))
  have hr17p15 : wordMatrix wr17p15 = M 220 :=
    (wordMatrix_append wr17p14 wg4).trans
      ((congrArg₂ (· * ·) hr17p14 hg4).trans (hlast 71))
  have hr17p16 : wordMatrix wr17p16 = M 134 :=
    (wordMatrix_append wr17p15 wg83).trans
      ((congrArg₂ (· * ·) hr17p15 hg83).trans (hlast 72))
  have hr17p17 : wordMatrix wr17p17 = M 0 :=
    (wordMatrix_append wr17p16 wg80).trans
      ((congrArg₂ (· * ·) hr17p16 hg80).trans (hlast 73))
  have hr18p0 : wordMatrix wr18p0 = M 221 :=
    (wordMatrix_append wB wg36).trans
      ((congrArg₂ (· * ·) hB hg36).trans (hlast 74))
  have hr18p1 : wordMatrix wr18p1 = M 222 :=
    (wordMatrix_append wr18p0 wg110).trans
      ((congrArg₂ (· * ·) hr18p0 hg110).trans (hlast 75))
  have hr18p2 : wordMatrix wr18p2 = M 223 :=
    (wordMatrix_append wr18p1 wg27).trans
      ((congrArg₂ (· * ·) hr18p1 hg27).trans (hlast 76))
  have hr18p3 : wordMatrix wr18p3 = M 224 :=
    (wordMatrix_append wr18p2 wg61).trans
      ((congrArg₂ (· * ·) hr18p2 hg61).trans (hlast 77))
  have hr18p4 : wordMatrix wr18p4 = M 225 :=
    (wordMatrix_append wr18p3 wg45).trans
      ((congrArg₂ (· * ·) hr18p3 hg45).trans (hlast 78))
  have hr18p5 : wordMatrix wr18p5 = M 226 :=
    (wordMatrix_append wr18p4 wg18).trans
      ((congrArg₂ (· * ·) hr18p4 hg18).trans (hlast 79))
  have hr18p6 : wordMatrix wr18p6 = M 227 :=
    (wordMatrix_append wr18p5 wg61).trans
      ((congrArg₂ (· * ·) hr18p5 hg61).trans (hlast 80))
  have hr18p7 : wordMatrix wr18p7 = M 228 :=
    (wordMatrix_append wr18p6 wg5).trans
      ((congrArg₂ (· * ·) hr18p6 hg5).trans (hlast 81))
  have hr18p8 : wordMatrix wr18p8 = M 140 :=
    (wordMatrix_append wr18p7 wg48).trans
      ((congrArg₂ (· * ·) hr18p7 hg48).trans (hlast 82))
  have hr18p9 : wordMatrix wr18p9 = M 0 :=
    (wordMatrix_append wr18p8 wg84).trans
      ((congrArg₂ (· * ·) hr18p8 hg84).trans (hlast 83))
  have hr19p0 : wordMatrix wr19p0 = M 229 :=
    (wordMatrix_append wB wg6).trans
      ((congrArg₂ (· * ·) hB hg6).trans (hlast 84))
  have hr19p1 : wordMatrix wr19p1 = M 230 :=
    (wordMatrix_append wr19p0 wg110).trans
      ((congrArg₂ (· * ·) hr19p0 hg110).trans (hlast 85))
  have hr19p2 : wordMatrix wr19p2 = M 231 :=
    (wordMatrix_append wr19p1 wg44).trans
      ((congrArg₂ (· * ·) hr19p1 hg44).trans (hlast 86))
  have hr19p3 : wordMatrix wr19p3 = M 232 :=
    (wordMatrix_append wr19p2 wg29).trans
      ((congrArg₂ (· * ·) hr19p2 hg29).trans (hlast 87))
  have hr19p4 : wordMatrix wr19p4 = M 233 :=
    (wordMatrix_append wr19p3 wg66).trans
      ((congrArg₂ (· * ·) hr19p3 hg66).trans (hlast 88))
  have hr19p5 : wordMatrix wr19p5 = M 234 :=
    (wordMatrix_append wr19p4 wg34).trans
      ((congrArg₂ (· * ·) hr19p4 hg34).trans (hlast 89))
  have hr19p6 : wordMatrix wr19p6 = M 235 :=
    (wordMatrix_append wr19p5 wg4).trans
      ((congrArg₂ (· * ·) hr19p5 hg4).trans (hlast 90))
  have hr19p7 : wordMatrix wr19p7 = M 236 :=
    (wordMatrix_append wr19p6 wg14).trans
      ((congrArg₂ (· * ·) hr19p6 hg14).trans (hlast 91))
  have hr19p8 : wordMatrix wr19p8 = M 237 :=
    (wordMatrix_append wr19p7 wg37).trans
      ((congrArg₂ (· * ·) hr19p7 hg37).trans (hlast 92))
  have hr19p9 : wordMatrix wr19p9 = M 238 :=
    (wordMatrix_append wr19p8 wg34).trans
      ((congrArg₂ (· * ·) hr19p8 hg34).trans (hlast 93))
  have hr19p10 : wordMatrix wr19p10 = M 1 :=
    (wordMatrix_append wr19p9 wg77).trans
      ((congrArg₂ (· * ·) hr19p9 hg77).trans (hlast 94))
  have hr19p11 : wordMatrix wr19p11 = M 0 :=
    (wordMatrix_append wr19p10 wa).trans
      ((congrArg₂ (· * ·) hr19p10 ha).trans (hlast 95))
  have hr20p0 : wordMatrix wr20p0 = M 239 :=
    (wordMatrix_append wg4 wg25).trans
      ((congrArg₂ (· * ·) hg4 hg25).trans (hlast 96))
  have hr20p1 : wordMatrix wr20p1 = M 240 :=
    (wordMatrix_append wr20p0 wg10).trans
      ((congrArg₂ (· * ·) hr20p0 hg10).trans (hlast 97))
  have hr20p2 : wordMatrix wr20p2 = M 241 :=
    (wordMatrix_append wr20p1 wg39).trans
      ((congrArg₂ (· * ·) hr20p1 hg39).trans (hlast 98))
  have hr20p3 : wordMatrix wr20p3 = M 242 :=
    (wordMatrix_append wr20p2 wg111).trans
      ((congrArg₂ (· * ·) hr20p2 hg111).trans (hlast 99))
  have hr20p4 : wordMatrix wr20p4 = M 243 :=
    (wordMatrix_append wr20p3 wg17).trans
      ((congrArg₂ (· * ·) hr20p3 hg17).trans (hlast 100))
  have hr20p5 : wordMatrix wr20p5 = M 244 :=
    (wordMatrix_append wr20p4 wg47).trans
      ((congrArg₂ (· * ·) hr20p4 hg47).trans (hlast 101))
  have hr20p6 : wordMatrix wr20p6 = M 245 :=
    (wordMatrix_append wr20p5 wg8).trans
      ((congrArg₂ (· * ·) hr20p5 hg8).trans (hlast 102))
  have hr20p7 : wordMatrix wr20p7 = M 246 :=
    (wordMatrix_append wr20p6 wg34).trans
      ((congrArg₂ (· * ·) hr20p6 hg34).trans (hlast 103))
  have hr20p8 : wordMatrix wr20p8 = M 247 :=
    (wordMatrix_append wr20p7 wg40).trans
      ((congrArg₂ (· * ·) hr20p7 hg40).trans (hlast 104))
  have hr20p9 : wordMatrix wr20p9 = M 194 :=
    (wordMatrix_append wr20p8 wg66).trans
      ((congrArg₂ (· * ·) hr20p8 hg66).trans (hlast 105))
  have hr20p10 : wordMatrix wr20p10 = M 0 :=
    (wordMatrix_append wr20p9 wg102).trans
      ((congrArg₂ (· * ·) hr20p9 hg102).trans (hlast 106))
  have hr21p0 : wordMatrix wr21p0 = M 248 :=
    (wordMatrix_append wg4 wg37).trans
      ((congrArg₂ (· * ·) hg4 hg37).trans (hlast 107))
  have hr21p1 : wordMatrix wr21p1 = M 249 :=
    (wordMatrix_append wr21p0 wg111).trans
      ((congrArg₂ (· * ·) hr21p0 hg111).trans (hlast 108))
  have hr21p2 : wordMatrix wr21p2 = M 250 :=
    (wordMatrix_append wr21p1 wg40).trans
      ((congrArg₂ (· * ·) hr21p1 hg40).trans (hlast 109))
  have hr21p3 : wordMatrix wr21p3 = M 251 :=
    (wordMatrix_append wr21p2 wg17).trans
      ((congrArg₂ (· * ·) hr21p2 hg17).trans (hlast 110))
  have hr21p4 : wordMatrix wr21p4 = M 252 :=
    (wordMatrix_append wr21p3 wg29).trans
      ((congrArg₂ (· * ·) hr21p3 hg29).trans (hlast 111))
  have hr21p5 : wordMatrix wr21p5 = M 253 :=
    (wordMatrix_append wr21p4 wg29).trans
      ((congrArg₂ (· * ·) hr21p4 hg29).trans (hlast 112))
  have hr21p6 : wordMatrix wr21p6 = M 254 :=
    (wordMatrix_append wr21p5 wg18).trans
      ((congrArg₂ (· * ·) hr21p5 hg18).trans (hlast 113))
  have hr21p7 : wordMatrix wr21p7 = M 255 :=
    (wordMatrix_append wr21p6 wg112).trans
      ((congrArg₂ (· * ·) hr21p6 hg112).trans (hlast 114))
  have hr21p8 : wordMatrix wr21p8 = M 256 :=
    (wordMatrix_append wr21p7 wg101).trans
      ((congrArg₂ (· * ·) hr21p7 hg101).trans (hlast 115))
  have hr21p9 : wordMatrix wr21p9 = M 257 :=
    (wordMatrix_append wr21p8 wg15).trans
      ((congrArg₂ (· * ·) hr21p8 hg15).trans (hlast 116))
  have hr21p10 : wordMatrix wr21p10 = M 258 :=
    (wordMatrix_append wr21p9 wg3).trans
      ((congrArg₂ (· * ·) hr21p9 hg3).trans (hlast 117))
  have hr21p11 : wordMatrix wr21p11 = M 259 :=
    (wordMatrix_append wr21p10 wg1).trans
      ((congrArg₂ (· * ·) hr21p10 hg1).trans (hlast 118))
  have hr21p12 : wordMatrix wr21p12 = M 260 :=
    (wordMatrix_append wr21p11 wg112).trans
      ((congrArg₂ (· * ·) hr21p11 hg112).trans (hlast 119))
  have hr21p13 : wordMatrix wr21p13 = M 0 :=
    (wordMatrix_append wr21p12 wg2).trans
      ((congrArg₂ (· * ·) hr21p12 hg2).trans (hlast 120))
  have rel0 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 0) = 1 := by
    apply relation_of_wordMatrix 0
    have he := literal_word0
    exact (congrArg wordMatrix he).trans (hr0p0.trans hseed.1)
  have rel1 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 1) = 1 := by
    apply relation_of_wordMatrix 1
    have he := literal_word1
    exact (congrArg wordMatrix he).trans (hr1p0.trans hseed.1)
  have rel2 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 2) = 1 := by
    apply relation_of_wordMatrix 2
    have he := literal_word2
    exact (congrArg wordMatrix he).trans (hr2p1.trans hseed.1)
  have rel3 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 3) = 1 := by
    apply relation_of_wordMatrix 3
    have he := literal_word3
    exact (congrArg wordMatrix he).trans (hr3p2.trans hseed.1)
  have rel4 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 4) = 1 := by
    apply relation_of_wordMatrix 4
    have he := literal_word4
    exact (congrArg wordMatrix he).trans (hr4p7.trans hseed.1)
  have rel5 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 5) = 1 := by
    apply relation_of_wordMatrix 5
    have he := literal_word5
    exact (congrArg wordMatrix he).trans (hr5p3.trans hseed.1)
  have rel6 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 6) = 1 := by
    apply relation_of_wordMatrix 6
    have he := literal_word6
    exact (congrArg wordMatrix he).trans (hr6p5.trans hseed.1)
  have rel7 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 7) = 1 := by
    apply relation_of_wordMatrix 7
    have he := literal_word7
    exact (congrArg wordMatrix he).trans (hr7p3.trans hseed.1)
  have rel8 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 8) = 1 := by
    apply relation_of_wordMatrix 8
    have he := literal_word8
    exact (congrArg wordMatrix he).trans (hr8p6.trans hseed.1)
  have rel9 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 9) = 1 := by
    apply relation_of_wordMatrix 9
    have he := literal_word9
    exact (congrArg wordMatrix he).trans (hr9p7.trans hseed.1)
  have rel10 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 10) = 1 := by
    apply relation_of_wordMatrix 10
    have he := literal_word10
    exact (congrArg wordMatrix he).trans (hr10p10.trans hseed.1)
  have rel11 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 11) = 1 := by
    apply relation_of_wordMatrix 11
    have he := literal_word11
    exact (congrArg wordMatrix he).trans (hr11p8.trans hseed.1)
  have rel12 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 12) = 1 := by
    apply relation_of_wordMatrix 12
    have he := literal_word12
    exact (congrArg wordMatrix he).trans (hr12p4.trans hseed.1)
  have rel13 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 13) = 1 := by
    apply relation_of_wordMatrix 13
    have he := literal_word13
    exact (congrArg wordMatrix he).trans (hr13p10.trans hseed.1)
  have rel14 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 14) = 1 := by
    apply relation_of_wordMatrix 14
    have he := literal_word14
    exact (congrArg wordMatrix he).trans (hr14p11.trans hseed.1)
  have rel15 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 15) = 1 := by
    apply relation_of_wordMatrix 15
    have he := literal_word15
    exact (congrArg wordMatrix he).trans (hr15p6.trans hseed.1)
  have rel16 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 16) = 1 := by
    apply relation_of_wordMatrix 16
    have he := literal_word16
    exact (congrArg wordMatrix he).trans (hr16p11.trans hseed.1)
  have rel17 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 17) = 1 := by
    apply relation_of_wordMatrix 17
    have he := literal_word17
    exact (congrArg wordMatrix he).trans (hr17p17.trans hseed.1)
  have rel18 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 18) = 1 := by
    apply relation_of_wordMatrix 18
    have he := literal_word18
    exact (congrArg wordMatrix he).trans (hr18p9.trans hseed.1)
  have rel19 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 19) = 1 := by
    apply relation_of_wordMatrix 19
    have he := literal_word19
    exact (congrArg wordMatrix he).trans (hr19p11.trans hseed.1)
  have rel20 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 20) = 1 := by
    apply relation_of_wordMatrix 20
    have he := literal_word20
    exact (congrArg wordMatrix he).trans (hr20p10.trans hseed.1)
  have rel21 : FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator 21) = 1 := by
    apply relation_of_wordMatrix 21
    have he := literal_word21
    exact (congrArg wordMatrix he).trans (hr21p13.trans hseed.1)
  exact allFin22 rel0 rel1 rel2 rel3 rel4 rel5 rel6 rel7 rel8 rel9 rel10 rel11 rel12 rel13 rel14 rel15 rel16 rel17 rel18 rel19 rel20 rel21

/-- Matrix arithmetic suffices to establish the exact fixed presentation relations. -/
public theorem localPresentationRelations_of_certificates
    (hseed : SeedIdentities) (hshared : SharedIdentities)
    (hfirst : FirstIdentities) (hlast : LastIdentities) : LocalPresentationRelations :=
  assemble (fun i => decode (matrixRows i)) hseed hshared hfirst hlast

/-- The exact ATLAS local generators satisfy all 22 fixed presentation relations. -/
public theorem localPresentationRelations : LocalPresentationRelations :=
  localPresentationRelations_of_certificates
    seedIdentities sharedIdentities firstIdentities lastIdentities

end Lyons.OrderCertificate
