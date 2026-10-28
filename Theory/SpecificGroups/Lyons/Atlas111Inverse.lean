module

public import Theory.SpecificGroups.Lyons.Atlas111InversePart0
public import Theory.SpecificGroups.Lyons.Atlas111InversePart1
public import Theory.SpecificGroups.Lyons.Atlas111InversePart2
public import Theory.SpecificGroups.Lyons.Atlas111InversePart3

/-!
# Certified inverses for the ATLAS Lyons matrices

The row certificates cover all 111 rows. The soundness theorem for packed
dot products then gives the two inverse identities in the actual matrix algebra.
Source matrices and their transcription are recorded in `Atlas111Source/`.
-/

namespace Lyons
open Atlas111Certificate

set_option maxRecDepth 10000 in
private theorem inverseA_rows : ∀ i, checkRow atlasARows atlasAInvColumns i = true :=
  (Fin.cases inverseA_row0
    (Fin.cases inverseA_row1
    (Fin.cases inverseA_row2
    (Fin.cases inverseA_row3
    (Fin.cases inverseA_row4
    (Fin.cases inverseA_row5
    (Fin.cases inverseA_row6
    (Fin.cases inverseA_row7
    (Fin.cases inverseA_row8
    (Fin.cases inverseA_row9
    (Fin.cases inverseA_row10
    (Fin.cases inverseA_row11
    (Fin.cases inverseA_row12
    (Fin.cases inverseA_row13
    (Fin.cases inverseA_row14
    (Fin.cases inverseA_row15
    (Fin.cases inverseA_row16
    (Fin.cases inverseA_row17
    (Fin.cases inverseA_row18
    (Fin.cases inverseA_row19
    (Fin.cases inverseA_row20
    (Fin.cases inverseA_row21
    (Fin.cases inverseA_row22
    (Fin.cases inverseA_row23
    (Fin.cases inverseA_row24
    (Fin.cases inverseA_row25
    (Fin.cases inverseA_row26
    (Fin.cases inverseA_row27
    (Fin.cases inverseA_row28
    (Fin.cases inverseA_row29
    (Fin.cases inverseA_row30
    (Fin.cases inverseA_row31
    (Fin.cases inverseA_row32
    (Fin.cases inverseA_row33
    (Fin.cases inverseA_row34
    (Fin.cases inverseA_row35
    (Fin.cases inverseA_row36
    (Fin.cases inverseA_row37
    (Fin.cases inverseA_row38
    (Fin.cases inverseA_row39
    (Fin.cases inverseA_row40
    (Fin.cases inverseA_row41
    (Fin.cases inverseA_row42
    (Fin.cases inverseA_row43
    (Fin.cases inverseA_row44
    (Fin.cases inverseA_row45
    (Fin.cases inverseA_row46
    (Fin.cases inverseA_row47
    (Fin.cases inverseA_row48
    (Fin.cases inverseA_row49
    (Fin.cases inverseA_row50
    (Fin.cases inverseA_row51
    (Fin.cases inverseA_row52
    (Fin.cases inverseA_row53
    (Fin.cases inverseA_row54
    (Fin.cases inverseA_row55
    (Fin.cases inverseA_row56
    (Fin.cases inverseA_row57
    (Fin.cases inverseA_row58
    (Fin.cases inverseA_row59
    (Fin.cases inverseA_row60
    (Fin.cases inverseA_row61
    (Fin.cases inverseA_row62
    (Fin.cases inverseA_row63
    (Fin.cases inverseA_row64
    (Fin.cases inverseA_row65
    (Fin.cases inverseA_row66
    (Fin.cases inverseA_row67
    (Fin.cases inverseA_row68
    (Fin.cases inverseA_row69
    (Fin.cases inverseA_row70
    (Fin.cases inverseA_row71
    (Fin.cases inverseA_row72
    (Fin.cases inverseA_row73
    (Fin.cases inverseA_row74
    (Fin.cases inverseA_row75
    (Fin.cases inverseA_row76
    (Fin.cases inverseA_row77
    (Fin.cases inverseA_row78
    (Fin.cases inverseA_row79
    (Fin.cases inverseA_row80
    (Fin.cases inverseA_row81
    (Fin.cases inverseA_row82
    (Fin.cases inverseA_row83
    (Fin.cases inverseA_row84
    (Fin.cases inverseA_row85
    (Fin.cases inverseA_row86
    (Fin.cases inverseA_row87
    (Fin.cases inverseA_row88
    (Fin.cases inverseA_row89
    (Fin.cases inverseA_row90
    (Fin.cases inverseA_row91
    (Fin.cases inverseA_row92
    (Fin.cases inverseA_row93
    (Fin.cases inverseA_row94
    (Fin.cases inverseA_row95
    (Fin.cases inverseA_row96
    (Fin.cases inverseA_row97
    (Fin.cases inverseA_row98
    (Fin.cases inverseA_row99
    (Fin.cases inverseA_row100
    (Fin.cases inverseA_row101
    (Fin.cases inverseA_row102
    (Fin.cases inverseA_row103
    (Fin.cases inverseA_row104
    (Fin.cases inverseA_row105
    (Fin.cases inverseA_row106
    (Fin.cases inverseA_row107
    (Fin.cases inverseA_row108
    (Fin.cases inverseA_row109
    (Fin.cases inverseA_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The supplied inverse candidate is a right inverse for the ATLAS generator. -/
public theorem atlasAMatrix_mul_inverse : atlasAMatrix * atlasAInvMatrix = 1 := by
  funext i j
  exact (packedDot_eq 111 (atlasARows i) (atlasAInvColumns j)).symm.trans
    (row_sound atlasARows atlasAInvColumns i (inverseA_rows i) j)

set_option maxRecDepth 10000 in
private theorem inverseB_rows : ∀ i, checkRow atlasBRows atlasBInvColumns i = true :=
  (Fin.cases inverseB_row0
    (Fin.cases inverseB_row1
    (Fin.cases inverseB_row2
    (Fin.cases inverseB_row3
    (Fin.cases inverseB_row4
    (Fin.cases inverseB_row5
    (Fin.cases inverseB_row6
    (Fin.cases inverseB_row7
    (Fin.cases inverseB_row8
    (Fin.cases inverseB_row9
    (Fin.cases inverseB_row10
    (Fin.cases inverseB_row11
    (Fin.cases inverseB_row12
    (Fin.cases inverseB_row13
    (Fin.cases inverseB_row14
    (Fin.cases inverseB_row15
    (Fin.cases inverseB_row16
    (Fin.cases inverseB_row17
    (Fin.cases inverseB_row18
    (Fin.cases inverseB_row19
    (Fin.cases inverseB_row20
    (Fin.cases inverseB_row21
    (Fin.cases inverseB_row22
    (Fin.cases inverseB_row23
    (Fin.cases inverseB_row24
    (Fin.cases inverseB_row25
    (Fin.cases inverseB_row26
    (Fin.cases inverseB_row27
    (Fin.cases inverseB_row28
    (Fin.cases inverseB_row29
    (Fin.cases inverseB_row30
    (Fin.cases inverseB_row31
    (Fin.cases inverseB_row32
    (Fin.cases inverseB_row33
    (Fin.cases inverseB_row34
    (Fin.cases inverseB_row35
    (Fin.cases inverseB_row36
    (Fin.cases inverseB_row37
    (Fin.cases inverseB_row38
    (Fin.cases inverseB_row39
    (Fin.cases inverseB_row40
    (Fin.cases inverseB_row41
    (Fin.cases inverseB_row42
    (Fin.cases inverseB_row43
    (Fin.cases inverseB_row44
    (Fin.cases inverseB_row45
    (Fin.cases inverseB_row46
    (Fin.cases inverseB_row47
    (Fin.cases inverseB_row48
    (Fin.cases inverseB_row49
    (Fin.cases inverseB_row50
    (Fin.cases inverseB_row51
    (Fin.cases inverseB_row52
    (Fin.cases inverseB_row53
    (Fin.cases inverseB_row54
    (Fin.cases inverseB_row55
    (Fin.cases inverseB_row56
    (Fin.cases inverseB_row57
    (Fin.cases inverseB_row58
    (Fin.cases inverseB_row59
    (Fin.cases inverseB_row60
    (Fin.cases inverseB_row61
    (Fin.cases inverseB_row62
    (Fin.cases inverseB_row63
    (Fin.cases inverseB_row64
    (Fin.cases inverseB_row65
    (Fin.cases inverseB_row66
    (Fin.cases inverseB_row67
    (Fin.cases inverseB_row68
    (Fin.cases inverseB_row69
    (Fin.cases inverseB_row70
    (Fin.cases inverseB_row71
    (Fin.cases inverseB_row72
    (Fin.cases inverseB_row73
    (Fin.cases inverseB_row74
    (Fin.cases inverseB_row75
    (Fin.cases inverseB_row76
    (Fin.cases inverseB_row77
    (Fin.cases inverseB_row78
    (Fin.cases inverseB_row79
    (Fin.cases inverseB_row80
    (Fin.cases inverseB_row81
    (Fin.cases inverseB_row82
    (Fin.cases inverseB_row83
    (Fin.cases inverseB_row84
    (Fin.cases inverseB_row85
    (Fin.cases inverseB_row86
    (Fin.cases inverseB_row87
    (Fin.cases inverseB_row88
    (Fin.cases inverseB_row89
    (Fin.cases inverseB_row90
    (Fin.cases inverseB_row91
    (Fin.cases inverseB_row92
    (Fin.cases inverseB_row93
    (Fin.cases inverseB_row94
    (Fin.cases inverseB_row95
    (Fin.cases inverseB_row96
    (Fin.cases inverseB_row97
    (Fin.cases inverseB_row98
    (Fin.cases inverseB_row99
    (Fin.cases inverseB_row100
    (Fin.cases inverseB_row101
    (Fin.cases inverseB_row102
    (Fin.cases inverseB_row103
    (Fin.cases inverseB_row104
    (Fin.cases inverseB_row105
    (Fin.cases inverseB_row106
    (Fin.cases inverseB_row107
    (Fin.cases inverseB_row108
    (Fin.cases inverseB_row109
    (Fin.cases inverseB_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The supplied inverse candidate is a right inverse for the ATLAS generator. -/
public theorem atlasBMatrix_mul_inverse : atlasBMatrix * atlasBInvMatrix = 1 := by
  funext i j
  exact (packedDot_eq 111 (atlasBRows i) (atlasBInvColumns j)).symm.trans
    (row_sound atlasBRows atlasBInvColumns i (inverseB_rows i) j)

end Lyons
