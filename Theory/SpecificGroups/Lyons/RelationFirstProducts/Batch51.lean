module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts

/-!
# Checked packed products for the local presentation

Each row equality is checked by kernel reduction. The proved packed-row
soundness theorem converts the checks to ordinary matrix multiplication.
Source data and reproducible generation: `Atlas111LocalRelationSource/`.
-/

namespace Lyons.RelationCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid10 : checkValid m10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row0 :
    checkProductRow m154 m10 m155 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row1 :
    checkProductRow m154 m10 m155 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row2 :
    checkProductRow m154 m10 m155 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row3 :
    checkProductRow m154 m10 m155 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row4 :
    checkProductRow m154 m10 m155 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row5 :
    checkProductRow m154 m10 m155 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row6 :
    checkProductRow m154 m10 m155 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row7 :
    checkProductRow m154 m10 m155 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row8 :
    checkProductRow m154 m10 m155 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row9 :
    checkProductRow m154 m10 m155 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row10 :
    checkProductRow m154 m10 m155 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row11 :
    checkProductRow m154 m10 m155 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row12 :
    checkProductRow m154 m10 m155 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row13 :
    checkProductRow m154 m10 m155 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row14 :
    checkProductRow m154 m10 m155 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row15 :
    checkProductRow m154 m10 m155 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row16 :
    checkProductRow m154 m10 m155 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row17 :
    checkProductRow m154 m10 m155 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row18 :
    checkProductRow m154 m10 m155 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row19 :
    checkProductRow m154 m10 m155 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row20 :
    checkProductRow m154 m10 m155 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row21 :
    checkProductRow m154 m10 m155 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row22 :
    checkProductRow m154 m10 m155 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row23 :
    checkProductRow m154 m10 m155 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row24 :
    checkProductRow m154 m10 m155 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row25 :
    checkProductRow m154 m10 m155 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row26 :
    checkProductRow m154 m10 m155 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row27 :
    checkProductRow m154 m10 m155 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row28 :
    checkProductRow m154 m10 m155 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row29 :
    checkProductRow m154 m10 m155 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row30 :
    checkProductRow m154 m10 m155 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row31 :
    checkProductRow m154 m10 m155 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row32 :
    checkProductRow m154 m10 m155 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row33 :
    checkProductRow m154 m10 m155 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row34 :
    checkProductRow m154 m10 m155 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row35 :
    checkProductRow m154 m10 m155 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row36 :
    checkProductRow m154 m10 m155 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row37 :
    checkProductRow m154 m10 m155 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row38 :
    checkProductRow m154 m10 m155 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row39 :
    checkProductRow m154 m10 m155 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row40 :
    checkProductRow m154 m10 m155 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row41 :
    checkProductRow m154 m10 m155 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row42 :
    checkProductRow m154 m10 m155 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row43 :
    checkProductRow m154 m10 m155 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row44 :
    checkProductRow m154 m10 m155 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row45 :
    checkProductRow m154 m10 m155 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row46 :
    checkProductRow m154 m10 m155 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row47 :
    checkProductRow m154 m10 m155 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row48 :
    checkProductRow m154 m10 m155 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row49 :
    checkProductRow m154 m10 m155 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row50 :
    checkProductRow m154 m10 m155 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row51 :
    checkProductRow m154 m10 m155 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row52 :
    checkProductRow m154 m10 m155 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row53 :
    checkProductRow m154 m10 m155 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row54 :
    checkProductRow m154 m10 m155 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row55 :
    checkProductRow m154 m10 m155 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row56 :
    checkProductRow m154 m10 m155 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row57 :
    checkProductRow m154 m10 m155 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row58 :
    checkProductRow m154 m10 m155 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row59 :
    checkProductRow m154 m10 m155 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row60 :
    checkProductRow m154 m10 m155 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row61 :
    checkProductRow m154 m10 m155 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row62 :
    checkProductRow m154 m10 m155 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row63 :
    checkProductRow m154 m10 m155 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row64 :
    checkProductRow m154 m10 m155 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row65 :
    checkProductRow m154 m10 m155 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row66 :
    checkProductRow m154 m10 m155 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row67 :
    checkProductRow m154 m10 m155 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row68 :
    checkProductRow m154 m10 m155 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row69 :
    checkProductRow m154 m10 m155 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row70 :
    checkProductRow m154 m10 m155 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row71 :
    checkProductRow m154 m10 m155 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row72 :
    checkProductRow m154 m10 m155 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row73 :
    checkProductRow m154 m10 m155 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row74 :
    checkProductRow m154 m10 m155 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row75 :
    checkProductRow m154 m10 m155 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row76 :
    checkProductRow m154 m10 m155 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row77 :
    checkProductRow m154 m10 m155 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row78 :
    checkProductRow m154 m10 m155 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row79 :
    checkProductRow m154 m10 m155 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row80 :
    checkProductRow m154 m10 m155 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row81 :
    checkProductRow m154 m10 m155 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row82 :
    checkProductRow m154 m10 m155 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row83 :
    checkProductRow m154 m10 m155 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row84 :
    checkProductRow m154 m10 m155 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row85 :
    checkProductRow m154 m10 m155 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row86 :
    checkProductRow m154 m10 m155 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row87 :
    checkProductRow m154 m10 m155 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row88 :
    checkProductRow m154 m10 m155 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row89 :
    checkProductRow m154 m10 m155 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row90 :
    checkProductRow m154 m10 m155 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row91 :
    checkProductRow m154 m10 m155 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row92 :
    checkProductRow m154 m10 m155 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row93 :
    checkProductRow m154 m10 m155 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row94 :
    checkProductRow m154 m10 m155 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row95 :
    checkProductRow m154 m10 m155 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row96 :
    checkProductRow m154 m10 m155 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row97 :
    checkProductRow m154 m10 m155 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row98 :
    checkProductRow m154 m10 m155 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row99 :
    checkProductRow m154 m10 m155 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row100 :
    checkProductRow m154 m10 m155 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row101 :
    checkProductRow m154 m10 m155 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row102 :
    checkProductRow m154 m10 m155 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row103 :
    checkProductRow m154 m10 m155 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row104 :
    checkProductRow m154 m10 m155 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row105 :
    checkProductRow m154 m10 m155 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row106 :
    checkProductRow m154 m10 m155 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row107 :
    checkProductRow m154 m10 m155 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row108 :
    checkProductRow m154 m10 m155 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row109 :
    checkProductRow m154 m10 m155 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first51_row110 :
    checkProductRow m154 m10 m155 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product51 :
    decode (matrixRows 154) * decode (matrixRows 10) = decode (matrixRows 155) :=
  product_of_checked_rows m154 m10 m155 valid10
    (Fin.cases first51_row0
    (Fin.cases first51_row1
    (Fin.cases first51_row2
    (Fin.cases first51_row3
    (Fin.cases first51_row4
    (Fin.cases first51_row5
    (Fin.cases first51_row6
    (Fin.cases first51_row7
    (Fin.cases first51_row8
    (Fin.cases first51_row9
    (Fin.cases first51_row10
    (Fin.cases first51_row11
    (Fin.cases first51_row12
    (Fin.cases first51_row13
    (Fin.cases first51_row14
    (Fin.cases first51_row15
    (Fin.cases first51_row16
    (Fin.cases first51_row17
    (Fin.cases first51_row18
    (Fin.cases first51_row19
    (Fin.cases first51_row20
    (Fin.cases first51_row21
    (Fin.cases first51_row22
    (Fin.cases first51_row23
    (Fin.cases first51_row24
    (Fin.cases first51_row25
    (Fin.cases first51_row26
    (Fin.cases first51_row27
    (Fin.cases first51_row28
    (Fin.cases first51_row29
    (Fin.cases first51_row30
    (Fin.cases first51_row31
    (Fin.cases first51_row32
    (Fin.cases first51_row33
    (Fin.cases first51_row34
    (Fin.cases first51_row35
    (Fin.cases first51_row36
    (Fin.cases first51_row37
    (Fin.cases first51_row38
    (Fin.cases first51_row39
    (Fin.cases first51_row40
    (Fin.cases first51_row41
    (Fin.cases first51_row42
    (Fin.cases first51_row43
    (Fin.cases first51_row44
    (Fin.cases first51_row45
    (Fin.cases first51_row46
    (Fin.cases first51_row47
    (Fin.cases first51_row48
    (Fin.cases first51_row49
    (Fin.cases first51_row50
    (Fin.cases first51_row51
    (Fin.cases first51_row52
    (Fin.cases first51_row53
    (Fin.cases first51_row54
    (Fin.cases first51_row55
    (Fin.cases first51_row56
    (Fin.cases first51_row57
    (Fin.cases first51_row58
    (Fin.cases first51_row59
    (Fin.cases first51_row60
    (Fin.cases first51_row61
    (Fin.cases first51_row62
    (Fin.cases first51_row63
    (Fin.cases first51_row64
    (Fin.cases first51_row65
    (Fin.cases first51_row66
    (Fin.cases first51_row67
    (Fin.cases first51_row68
    (Fin.cases first51_row69
    (Fin.cases first51_row70
    (Fin.cases first51_row71
    (Fin.cases first51_row72
    (Fin.cases first51_row73
    (Fin.cases first51_row74
    (Fin.cases first51_row75
    (Fin.cases first51_row76
    (Fin.cases first51_row77
    (Fin.cases first51_row78
    (Fin.cases first51_row79
    (Fin.cases first51_row80
    (Fin.cases first51_row81
    (Fin.cases first51_row82
    (Fin.cases first51_row83
    (Fin.cases first51_row84
    (Fin.cases first51_row85
    (Fin.cases first51_row86
    (Fin.cases first51_row87
    (Fin.cases first51_row88
    (Fin.cases first51_row89
    (Fin.cases first51_row90
    (Fin.cases first51_row91
    (Fin.cases first51_row92
    (Fin.cases first51_row93
    (Fin.cases first51_row94
    (Fin.cases first51_row95
    (Fin.cases first51_row96
    (Fin.cases first51_row97
    (Fin.cases first51_row98
    (Fin.cases first51_row99
    (Fin.cases first51_row100
    (Fin.cases first51_row101
    (Fin.cases first51_row102
    (Fin.cases first51_row103
    (Fin.cases first51_row104
    (Fin.cases first51_row105
    (Fin.cases first51_row106
    (Fin.cases first51_row107
    (Fin.cases first51_row108
    (Fin.cases first51_row109
    (Fin.cases first51_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row0 :
    checkProductRow m155 m10 m156 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row1 :
    checkProductRow m155 m10 m156 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row2 :
    checkProductRow m155 m10 m156 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row3 :
    checkProductRow m155 m10 m156 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row4 :
    checkProductRow m155 m10 m156 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row5 :
    checkProductRow m155 m10 m156 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row6 :
    checkProductRow m155 m10 m156 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row7 :
    checkProductRow m155 m10 m156 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row8 :
    checkProductRow m155 m10 m156 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row9 :
    checkProductRow m155 m10 m156 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row10 :
    checkProductRow m155 m10 m156 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row11 :
    checkProductRow m155 m10 m156 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row12 :
    checkProductRow m155 m10 m156 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row13 :
    checkProductRow m155 m10 m156 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row14 :
    checkProductRow m155 m10 m156 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row15 :
    checkProductRow m155 m10 m156 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row16 :
    checkProductRow m155 m10 m156 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row17 :
    checkProductRow m155 m10 m156 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row18 :
    checkProductRow m155 m10 m156 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row19 :
    checkProductRow m155 m10 m156 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row20 :
    checkProductRow m155 m10 m156 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row21 :
    checkProductRow m155 m10 m156 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row22 :
    checkProductRow m155 m10 m156 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row23 :
    checkProductRow m155 m10 m156 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row24 :
    checkProductRow m155 m10 m156 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row25 :
    checkProductRow m155 m10 m156 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row26 :
    checkProductRow m155 m10 m156 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row27 :
    checkProductRow m155 m10 m156 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row28 :
    checkProductRow m155 m10 m156 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row29 :
    checkProductRow m155 m10 m156 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row30 :
    checkProductRow m155 m10 m156 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row31 :
    checkProductRow m155 m10 m156 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row32 :
    checkProductRow m155 m10 m156 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row33 :
    checkProductRow m155 m10 m156 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row34 :
    checkProductRow m155 m10 m156 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row35 :
    checkProductRow m155 m10 m156 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row36 :
    checkProductRow m155 m10 m156 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row37 :
    checkProductRow m155 m10 m156 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row38 :
    checkProductRow m155 m10 m156 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row39 :
    checkProductRow m155 m10 m156 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row40 :
    checkProductRow m155 m10 m156 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row41 :
    checkProductRow m155 m10 m156 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row42 :
    checkProductRow m155 m10 m156 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row43 :
    checkProductRow m155 m10 m156 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row44 :
    checkProductRow m155 m10 m156 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row45 :
    checkProductRow m155 m10 m156 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row46 :
    checkProductRow m155 m10 m156 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row47 :
    checkProductRow m155 m10 m156 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row48 :
    checkProductRow m155 m10 m156 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row49 :
    checkProductRow m155 m10 m156 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row50 :
    checkProductRow m155 m10 m156 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row51 :
    checkProductRow m155 m10 m156 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row52 :
    checkProductRow m155 m10 m156 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row53 :
    checkProductRow m155 m10 m156 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row54 :
    checkProductRow m155 m10 m156 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row55 :
    checkProductRow m155 m10 m156 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row56 :
    checkProductRow m155 m10 m156 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row57 :
    checkProductRow m155 m10 m156 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row58 :
    checkProductRow m155 m10 m156 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row59 :
    checkProductRow m155 m10 m156 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row60 :
    checkProductRow m155 m10 m156 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row61 :
    checkProductRow m155 m10 m156 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row62 :
    checkProductRow m155 m10 m156 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row63 :
    checkProductRow m155 m10 m156 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row64 :
    checkProductRow m155 m10 m156 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row65 :
    checkProductRow m155 m10 m156 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row66 :
    checkProductRow m155 m10 m156 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row67 :
    checkProductRow m155 m10 m156 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row68 :
    checkProductRow m155 m10 m156 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row69 :
    checkProductRow m155 m10 m156 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row70 :
    checkProductRow m155 m10 m156 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row71 :
    checkProductRow m155 m10 m156 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row72 :
    checkProductRow m155 m10 m156 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row73 :
    checkProductRow m155 m10 m156 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row74 :
    checkProductRow m155 m10 m156 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row75 :
    checkProductRow m155 m10 m156 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row76 :
    checkProductRow m155 m10 m156 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row77 :
    checkProductRow m155 m10 m156 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row78 :
    checkProductRow m155 m10 m156 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row79 :
    checkProductRow m155 m10 m156 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row80 :
    checkProductRow m155 m10 m156 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row81 :
    checkProductRow m155 m10 m156 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row82 :
    checkProductRow m155 m10 m156 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row83 :
    checkProductRow m155 m10 m156 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row84 :
    checkProductRow m155 m10 m156 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row85 :
    checkProductRow m155 m10 m156 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row86 :
    checkProductRow m155 m10 m156 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row87 :
    checkProductRow m155 m10 m156 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row88 :
    checkProductRow m155 m10 m156 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row89 :
    checkProductRow m155 m10 m156 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row90 :
    checkProductRow m155 m10 m156 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row91 :
    checkProductRow m155 m10 m156 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row92 :
    checkProductRow m155 m10 m156 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row93 :
    checkProductRow m155 m10 m156 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row94 :
    checkProductRow m155 m10 m156 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row95 :
    checkProductRow m155 m10 m156 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row96 :
    checkProductRow m155 m10 m156 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row97 :
    checkProductRow m155 m10 m156 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row98 :
    checkProductRow m155 m10 m156 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row99 :
    checkProductRow m155 m10 m156 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row100 :
    checkProductRow m155 m10 m156 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row101 :
    checkProductRow m155 m10 m156 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row102 :
    checkProductRow m155 m10 m156 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row103 :
    checkProductRow m155 m10 m156 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row104 :
    checkProductRow m155 m10 m156 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row105 :
    checkProductRow m155 m10 m156 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row106 :
    checkProductRow m155 m10 m156 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row107 :
    checkProductRow m155 m10 m156 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row108 :
    checkProductRow m155 m10 m156 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row109 :
    checkProductRow m155 m10 m156 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first52_row110 :
    checkProductRow m155 m10 m156 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product52 :
    decode (matrixRows 155) * decode (matrixRows 10) = decode (matrixRows 156) :=
  product_of_checked_rows m155 m10 m156 valid10
    (Fin.cases first52_row0
    (Fin.cases first52_row1
    (Fin.cases first52_row2
    (Fin.cases first52_row3
    (Fin.cases first52_row4
    (Fin.cases first52_row5
    (Fin.cases first52_row6
    (Fin.cases first52_row7
    (Fin.cases first52_row8
    (Fin.cases first52_row9
    (Fin.cases first52_row10
    (Fin.cases first52_row11
    (Fin.cases first52_row12
    (Fin.cases first52_row13
    (Fin.cases first52_row14
    (Fin.cases first52_row15
    (Fin.cases first52_row16
    (Fin.cases first52_row17
    (Fin.cases first52_row18
    (Fin.cases first52_row19
    (Fin.cases first52_row20
    (Fin.cases first52_row21
    (Fin.cases first52_row22
    (Fin.cases first52_row23
    (Fin.cases first52_row24
    (Fin.cases first52_row25
    (Fin.cases first52_row26
    (Fin.cases first52_row27
    (Fin.cases first52_row28
    (Fin.cases first52_row29
    (Fin.cases first52_row30
    (Fin.cases first52_row31
    (Fin.cases first52_row32
    (Fin.cases first52_row33
    (Fin.cases first52_row34
    (Fin.cases first52_row35
    (Fin.cases first52_row36
    (Fin.cases first52_row37
    (Fin.cases first52_row38
    (Fin.cases first52_row39
    (Fin.cases first52_row40
    (Fin.cases first52_row41
    (Fin.cases first52_row42
    (Fin.cases first52_row43
    (Fin.cases first52_row44
    (Fin.cases first52_row45
    (Fin.cases first52_row46
    (Fin.cases first52_row47
    (Fin.cases first52_row48
    (Fin.cases first52_row49
    (Fin.cases first52_row50
    (Fin.cases first52_row51
    (Fin.cases first52_row52
    (Fin.cases first52_row53
    (Fin.cases first52_row54
    (Fin.cases first52_row55
    (Fin.cases first52_row56
    (Fin.cases first52_row57
    (Fin.cases first52_row58
    (Fin.cases first52_row59
    (Fin.cases first52_row60
    (Fin.cases first52_row61
    (Fin.cases first52_row62
    (Fin.cases first52_row63
    (Fin.cases first52_row64
    (Fin.cases first52_row65
    (Fin.cases first52_row66
    (Fin.cases first52_row67
    (Fin.cases first52_row68
    (Fin.cases first52_row69
    (Fin.cases first52_row70
    (Fin.cases first52_row71
    (Fin.cases first52_row72
    (Fin.cases first52_row73
    (Fin.cases first52_row74
    (Fin.cases first52_row75
    (Fin.cases first52_row76
    (Fin.cases first52_row77
    (Fin.cases first52_row78
    (Fin.cases first52_row79
    (Fin.cases first52_row80
    (Fin.cases first52_row81
    (Fin.cases first52_row82
    (Fin.cases first52_row83
    (Fin.cases first52_row84
    (Fin.cases first52_row85
    (Fin.cases first52_row86
    (Fin.cases first52_row87
    (Fin.cases first52_row88
    (Fin.cases first52_row89
    (Fin.cases first52_row90
    (Fin.cases first52_row91
    (Fin.cases first52_row92
    (Fin.cases first52_row93
    (Fin.cases first52_row94
    (Fin.cases first52_row95
    (Fin.cases first52_row96
    (Fin.cases first52_row97
    (Fin.cases first52_row98
    (Fin.cases first52_row99
    (Fin.cases first52_row100
    (Fin.cases first52_row101
    (Fin.cases first52_row102
    (Fin.cases first52_row103
    (Fin.cases first52_row104
    (Fin.cases first52_row105
    (Fin.cases first52_row106
    (Fin.cases first52_row107
    (Fin.cases first52_row108
    (Fin.cases first52_row109
    (Fin.cases first52_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid97 : checkValid m97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row0 :
    checkProductRow m156 m97 m116 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row1 :
    checkProductRow m156 m97 m116 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row2 :
    checkProductRow m156 m97 m116 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row3 :
    checkProductRow m156 m97 m116 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row4 :
    checkProductRow m156 m97 m116 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row5 :
    checkProductRow m156 m97 m116 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row6 :
    checkProductRow m156 m97 m116 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row7 :
    checkProductRow m156 m97 m116 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row8 :
    checkProductRow m156 m97 m116 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row9 :
    checkProductRow m156 m97 m116 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row10 :
    checkProductRow m156 m97 m116 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row11 :
    checkProductRow m156 m97 m116 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row12 :
    checkProductRow m156 m97 m116 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row13 :
    checkProductRow m156 m97 m116 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row14 :
    checkProductRow m156 m97 m116 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row15 :
    checkProductRow m156 m97 m116 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row16 :
    checkProductRow m156 m97 m116 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row17 :
    checkProductRow m156 m97 m116 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row18 :
    checkProductRow m156 m97 m116 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row19 :
    checkProductRow m156 m97 m116 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row20 :
    checkProductRow m156 m97 m116 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row21 :
    checkProductRow m156 m97 m116 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row22 :
    checkProductRow m156 m97 m116 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row23 :
    checkProductRow m156 m97 m116 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row24 :
    checkProductRow m156 m97 m116 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row25 :
    checkProductRow m156 m97 m116 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row26 :
    checkProductRow m156 m97 m116 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row27 :
    checkProductRow m156 m97 m116 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row28 :
    checkProductRow m156 m97 m116 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row29 :
    checkProductRow m156 m97 m116 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row30 :
    checkProductRow m156 m97 m116 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row31 :
    checkProductRow m156 m97 m116 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row32 :
    checkProductRow m156 m97 m116 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row33 :
    checkProductRow m156 m97 m116 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row34 :
    checkProductRow m156 m97 m116 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row35 :
    checkProductRow m156 m97 m116 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row36 :
    checkProductRow m156 m97 m116 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row37 :
    checkProductRow m156 m97 m116 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row38 :
    checkProductRow m156 m97 m116 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row39 :
    checkProductRow m156 m97 m116 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row40 :
    checkProductRow m156 m97 m116 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row41 :
    checkProductRow m156 m97 m116 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row42 :
    checkProductRow m156 m97 m116 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row43 :
    checkProductRow m156 m97 m116 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row44 :
    checkProductRow m156 m97 m116 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row45 :
    checkProductRow m156 m97 m116 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row46 :
    checkProductRow m156 m97 m116 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row47 :
    checkProductRow m156 m97 m116 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row48 :
    checkProductRow m156 m97 m116 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row49 :
    checkProductRow m156 m97 m116 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row50 :
    checkProductRow m156 m97 m116 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row51 :
    checkProductRow m156 m97 m116 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row52 :
    checkProductRow m156 m97 m116 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row53 :
    checkProductRow m156 m97 m116 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row54 :
    checkProductRow m156 m97 m116 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row55 :
    checkProductRow m156 m97 m116 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row56 :
    checkProductRow m156 m97 m116 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row57 :
    checkProductRow m156 m97 m116 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row58 :
    checkProductRow m156 m97 m116 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row59 :
    checkProductRow m156 m97 m116 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row60 :
    checkProductRow m156 m97 m116 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row61 :
    checkProductRow m156 m97 m116 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row62 :
    checkProductRow m156 m97 m116 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row63 :
    checkProductRow m156 m97 m116 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row64 :
    checkProductRow m156 m97 m116 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row65 :
    checkProductRow m156 m97 m116 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row66 :
    checkProductRow m156 m97 m116 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row67 :
    checkProductRow m156 m97 m116 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row68 :
    checkProductRow m156 m97 m116 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row69 :
    checkProductRow m156 m97 m116 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row70 :
    checkProductRow m156 m97 m116 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row71 :
    checkProductRow m156 m97 m116 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row72 :
    checkProductRow m156 m97 m116 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row73 :
    checkProductRow m156 m97 m116 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row74 :
    checkProductRow m156 m97 m116 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row75 :
    checkProductRow m156 m97 m116 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row76 :
    checkProductRow m156 m97 m116 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row77 :
    checkProductRow m156 m97 m116 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row78 :
    checkProductRow m156 m97 m116 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row79 :
    checkProductRow m156 m97 m116 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row80 :
    checkProductRow m156 m97 m116 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row81 :
    checkProductRow m156 m97 m116 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row82 :
    checkProductRow m156 m97 m116 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row83 :
    checkProductRow m156 m97 m116 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row84 :
    checkProductRow m156 m97 m116 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row85 :
    checkProductRow m156 m97 m116 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row86 :
    checkProductRow m156 m97 m116 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row87 :
    checkProductRow m156 m97 m116 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row88 :
    checkProductRow m156 m97 m116 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row89 :
    checkProductRow m156 m97 m116 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row90 :
    checkProductRow m156 m97 m116 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row91 :
    checkProductRow m156 m97 m116 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row92 :
    checkProductRow m156 m97 m116 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row93 :
    checkProductRow m156 m97 m116 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row94 :
    checkProductRow m156 m97 m116 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row95 :
    checkProductRow m156 m97 m116 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row96 :
    checkProductRow m156 m97 m116 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row97 :
    checkProductRow m156 m97 m116 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row98 :
    checkProductRow m156 m97 m116 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row99 :
    checkProductRow m156 m97 m116 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row100 :
    checkProductRow m156 m97 m116 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row101 :
    checkProductRow m156 m97 m116 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row102 :
    checkProductRow m156 m97 m116 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row103 :
    checkProductRow m156 m97 m116 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row104 :
    checkProductRow m156 m97 m116 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row105 :
    checkProductRow m156 m97 m116 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row106 :
    checkProductRow m156 m97 m116 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row107 :
    checkProductRow m156 m97 m116 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row108 :
    checkProductRow m156 m97 m116 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row109 :
    checkProductRow m156 m97 m116 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first53_row110 :
    checkProductRow m156 m97 m116 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product53 :
    decode (matrixRows 156) * decode (matrixRows 97) = decode (matrixRows 116) :=
  product_of_checked_rows m156 m97 m116 valid97
    (Fin.cases first53_row0
    (Fin.cases first53_row1
    (Fin.cases first53_row2
    (Fin.cases first53_row3
    (Fin.cases first53_row4
    (Fin.cases first53_row5
    (Fin.cases first53_row6
    (Fin.cases first53_row7
    (Fin.cases first53_row8
    (Fin.cases first53_row9
    (Fin.cases first53_row10
    (Fin.cases first53_row11
    (Fin.cases first53_row12
    (Fin.cases first53_row13
    (Fin.cases first53_row14
    (Fin.cases first53_row15
    (Fin.cases first53_row16
    (Fin.cases first53_row17
    (Fin.cases first53_row18
    (Fin.cases first53_row19
    (Fin.cases first53_row20
    (Fin.cases first53_row21
    (Fin.cases first53_row22
    (Fin.cases first53_row23
    (Fin.cases first53_row24
    (Fin.cases first53_row25
    (Fin.cases first53_row26
    (Fin.cases first53_row27
    (Fin.cases first53_row28
    (Fin.cases first53_row29
    (Fin.cases first53_row30
    (Fin.cases first53_row31
    (Fin.cases first53_row32
    (Fin.cases first53_row33
    (Fin.cases first53_row34
    (Fin.cases first53_row35
    (Fin.cases first53_row36
    (Fin.cases first53_row37
    (Fin.cases first53_row38
    (Fin.cases first53_row39
    (Fin.cases first53_row40
    (Fin.cases first53_row41
    (Fin.cases first53_row42
    (Fin.cases first53_row43
    (Fin.cases first53_row44
    (Fin.cases first53_row45
    (Fin.cases first53_row46
    (Fin.cases first53_row47
    (Fin.cases first53_row48
    (Fin.cases first53_row49
    (Fin.cases first53_row50
    (Fin.cases first53_row51
    (Fin.cases first53_row52
    (Fin.cases first53_row53
    (Fin.cases first53_row54
    (Fin.cases first53_row55
    (Fin.cases first53_row56
    (Fin.cases first53_row57
    (Fin.cases first53_row58
    (Fin.cases first53_row59
    (Fin.cases first53_row60
    (Fin.cases first53_row61
    (Fin.cases first53_row62
    (Fin.cases first53_row63
    (Fin.cases first53_row64
    (Fin.cases first53_row65
    (Fin.cases first53_row66
    (Fin.cases first53_row67
    (Fin.cases first53_row68
    (Fin.cases first53_row69
    (Fin.cases first53_row70
    (Fin.cases first53_row71
    (Fin.cases first53_row72
    (Fin.cases first53_row73
    (Fin.cases first53_row74
    (Fin.cases first53_row75
    (Fin.cases first53_row76
    (Fin.cases first53_row77
    (Fin.cases first53_row78
    (Fin.cases first53_row79
    (Fin.cases first53_row80
    (Fin.cases first53_row81
    (Fin.cases first53_row82
    (Fin.cases first53_row83
    (Fin.cases first53_row84
    (Fin.cases first53_row85
    (Fin.cases first53_row86
    (Fin.cases first53_row87
    (Fin.cases first53_row88
    (Fin.cases first53_row89
    (Fin.cases first53_row90
    (Fin.cases first53_row91
    (Fin.cases first53_row92
    (Fin.cases first53_row93
    (Fin.cases first53_row94
    (Fin.cases first53_row95
    (Fin.cases first53_row96
    (Fin.cases first53_row97
    (Fin.cases first53_row98
    (Fin.cases first53_row99
    (Fin.cases first53_row100
    (Fin.cases first53_row101
    (Fin.cases first53_row102
    (Fin.cases first53_row103
    (Fin.cases first53_row104
    (Fin.cases first53_row105
    (Fin.cases first53_row106
    (Fin.cases first53_row107
    (Fin.cases first53_row108
    (Fin.cases first53_row109
    (Fin.cases first53_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid4 : checkValid m4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row0 :
    checkProductRow m116 m4 m0 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row1 :
    checkProductRow m116 m4 m0 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row2 :
    checkProductRow m116 m4 m0 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row3 :
    checkProductRow m116 m4 m0 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row4 :
    checkProductRow m116 m4 m0 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row5 :
    checkProductRow m116 m4 m0 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row6 :
    checkProductRow m116 m4 m0 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row7 :
    checkProductRow m116 m4 m0 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row8 :
    checkProductRow m116 m4 m0 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row9 :
    checkProductRow m116 m4 m0 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row10 :
    checkProductRow m116 m4 m0 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row11 :
    checkProductRow m116 m4 m0 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row12 :
    checkProductRow m116 m4 m0 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row13 :
    checkProductRow m116 m4 m0 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row14 :
    checkProductRow m116 m4 m0 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row15 :
    checkProductRow m116 m4 m0 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row16 :
    checkProductRow m116 m4 m0 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row17 :
    checkProductRow m116 m4 m0 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row18 :
    checkProductRow m116 m4 m0 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row19 :
    checkProductRow m116 m4 m0 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row20 :
    checkProductRow m116 m4 m0 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row21 :
    checkProductRow m116 m4 m0 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row22 :
    checkProductRow m116 m4 m0 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row23 :
    checkProductRow m116 m4 m0 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row24 :
    checkProductRow m116 m4 m0 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row25 :
    checkProductRow m116 m4 m0 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row26 :
    checkProductRow m116 m4 m0 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row27 :
    checkProductRow m116 m4 m0 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row28 :
    checkProductRow m116 m4 m0 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row29 :
    checkProductRow m116 m4 m0 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row30 :
    checkProductRow m116 m4 m0 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row31 :
    checkProductRow m116 m4 m0 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row32 :
    checkProductRow m116 m4 m0 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row33 :
    checkProductRow m116 m4 m0 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row34 :
    checkProductRow m116 m4 m0 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row35 :
    checkProductRow m116 m4 m0 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row36 :
    checkProductRow m116 m4 m0 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row37 :
    checkProductRow m116 m4 m0 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row38 :
    checkProductRow m116 m4 m0 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row39 :
    checkProductRow m116 m4 m0 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row40 :
    checkProductRow m116 m4 m0 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row41 :
    checkProductRow m116 m4 m0 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row42 :
    checkProductRow m116 m4 m0 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row43 :
    checkProductRow m116 m4 m0 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row44 :
    checkProductRow m116 m4 m0 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row45 :
    checkProductRow m116 m4 m0 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row46 :
    checkProductRow m116 m4 m0 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row47 :
    checkProductRow m116 m4 m0 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row48 :
    checkProductRow m116 m4 m0 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row49 :
    checkProductRow m116 m4 m0 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row50 :
    checkProductRow m116 m4 m0 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row51 :
    checkProductRow m116 m4 m0 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row52 :
    checkProductRow m116 m4 m0 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row53 :
    checkProductRow m116 m4 m0 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row54 :
    checkProductRow m116 m4 m0 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row55 :
    checkProductRow m116 m4 m0 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row56 :
    checkProductRow m116 m4 m0 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row57 :
    checkProductRow m116 m4 m0 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row58 :
    checkProductRow m116 m4 m0 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row59 :
    checkProductRow m116 m4 m0 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row60 :
    checkProductRow m116 m4 m0 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row61 :
    checkProductRow m116 m4 m0 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row62 :
    checkProductRow m116 m4 m0 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row63 :
    checkProductRow m116 m4 m0 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row64 :
    checkProductRow m116 m4 m0 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row65 :
    checkProductRow m116 m4 m0 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row66 :
    checkProductRow m116 m4 m0 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row67 :
    checkProductRow m116 m4 m0 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row68 :
    checkProductRow m116 m4 m0 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row69 :
    checkProductRow m116 m4 m0 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row70 :
    checkProductRow m116 m4 m0 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row71 :
    checkProductRow m116 m4 m0 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row72 :
    checkProductRow m116 m4 m0 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row73 :
    checkProductRow m116 m4 m0 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row74 :
    checkProductRow m116 m4 m0 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row75 :
    checkProductRow m116 m4 m0 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row76 :
    checkProductRow m116 m4 m0 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row77 :
    checkProductRow m116 m4 m0 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row78 :
    checkProductRow m116 m4 m0 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row79 :
    checkProductRow m116 m4 m0 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row80 :
    checkProductRow m116 m4 m0 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row81 :
    checkProductRow m116 m4 m0 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row82 :
    checkProductRow m116 m4 m0 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row83 :
    checkProductRow m116 m4 m0 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row84 :
    checkProductRow m116 m4 m0 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row85 :
    checkProductRow m116 m4 m0 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row86 :
    checkProductRow m116 m4 m0 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row87 :
    checkProductRow m116 m4 m0 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row88 :
    checkProductRow m116 m4 m0 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row89 :
    checkProductRow m116 m4 m0 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row90 :
    checkProductRow m116 m4 m0 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row91 :
    checkProductRow m116 m4 m0 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row92 :
    checkProductRow m116 m4 m0 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row93 :
    checkProductRow m116 m4 m0 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row94 :
    checkProductRow m116 m4 m0 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row95 :
    checkProductRow m116 m4 m0 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row96 :
    checkProductRow m116 m4 m0 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row97 :
    checkProductRow m116 m4 m0 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row98 :
    checkProductRow m116 m4 m0 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row99 :
    checkProductRow m116 m4 m0 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row100 :
    checkProductRow m116 m4 m0 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row101 :
    checkProductRow m116 m4 m0 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row102 :
    checkProductRow m116 m4 m0 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row103 :
    checkProductRow m116 m4 m0 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row104 :
    checkProductRow m116 m4 m0 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row105 :
    checkProductRow m116 m4 m0 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row106 :
    checkProductRow m116 m4 m0 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row107 :
    checkProductRow m116 m4 m0 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row108 :
    checkProductRow m116 m4 m0 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row109 :
    checkProductRow m116 m4 m0 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first54_row110 :
    checkProductRow m116 m4 m0 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product54 :
    decode (matrixRows 116) * decode (matrixRows 4) = decode (matrixRows 0) :=
  product_of_checked_rows m116 m4 m0 valid4
    (Fin.cases first54_row0
    (Fin.cases first54_row1
    (Fin.cases first54_row2
    (Fin.cases first54_row3
    (Fin.cases first54_row4
    (Fin.cases first54_row5
    (Fin.cases first54_row6
    (Fin.cases first54_row7
    (Fin.cases first54_row8
    (Fin.cases first54_row9
    (Fin.cases first54_row10
    (Fin.cases first54_row11
    (Fin.cases first54_row12
    (Fin.cases first54_row13
    (Fin.cases first54_row14
    (Fin.cases first54_row15
    (Fin.cases first54_row16
    (Fin.cases first54_row17
    (Fin.cases first54_row18
    (Fin.cases first54_row19
    (Fin.cases first54_row20
    (Fin.cases first54_row21
    (Fin.cases first54_row22
    (Fin.cases first54_row23
    (Fin.cases first54_row24
    (Fin.cases first54_row25
    (Fin.cases first54_row26
    (Fin.cases first54_row27
    (Fin.cases first54_row28
    (Fin.cases first54_row29
    (Fin.cases first54_row30
    (Fin.cases first54_row31
    (Fin.cases first54_row32
    (Fin.cases first54_row33
    (Fin.cases first54_row34
    (Fin.cases first54_row35
    (Fin.cases first54_row36
    (Fin.cases first54_row37
    (Fin.cases first54_row38
    (Fin.cases first54_row39
    (Fin.cases first54_row40
    (Fin.cases first54_row41
    (Fin.cases first54_row42
    (Fin.cases first54_row43
    (Fin.cases first54_row44
    (Fin.cases first54_row45
    (Fin.cases first54_row46
    (Fin.cases first54_row47
    (Fin.cases first54_row48
    (Fin.cases first54_row49
    (Fin.cases first54_row50
    (Fin.cases first54_row51
    (Fin.cases first54_row52
    (Fin.cases first54_row53
    (Fin.cases first54_row54
    (Fin.cases first54_row55
    (Fin.cases first54_row56
    (Fin.cases first54_row57
    (Fin.cases first54_row58
    (Fin.cases first54_row59
    (Fin.cases first54_row60
    (Fin.cases first54_row61
    (Fin.cases first54_row62
    (Fin.cases first54_row63
    (Fin.cases first54_row64
    (Fin.cases first54_row65
    (Fin.cases first54_row66
    (Fin.cases first54_row67
    (Fin.cases first54_row68
    (Fin.cases first54_row69
    (Fin.cases first54_row70
    (Fin.cases first54_row71
    (Fin.cases first54_row72
    (Fin.cases first54_row73
    (Fin.cases first54_row74
    (Fin.cases first54_row75
    (Fin.cases first54_row76
    (Fin.cases first54_row77
    (Fin.cases first54_row78
    (Fin.cases first54_row79
    (Fin.cases first54_row80
    (Fin.cases first54_row81
    (Fin.cases first54_row82
    (Fin.cases first54_row83
    (Fin.cases first54_row84
    (Fin.cases first54_row85
    (Fin.cases first54_row86
    (Fin.cases first54_row87
    (Fin.cases first54_row88
    (Fin.cases first54_row89
    (Fin.cases first54_row90
    (Fin.cases first54_row91
    (Fin.cases first54_row92
    (Fin.cases first54_row93
    (Fin.cases first54_row94
    (Fin.cases first54_row95
    (Fin.cases first54_row96
    (Fin.cases first54_row97
    (Fin.cases first54_row98
    (Fin.cases first54_row99
    (Fin.cases first54_row100
    (Fin.cases first54_row101
    (Fin.cases first54_row102
    (Fin.cases first54_row103
    (Fin.cases first54_row104
    (Fin.cases first54_row105
    (Fin.cases first54_row106
    (Fin.cases first54_row107
    (Fin.cases first54_row108
    (Fin.cases first54_row109
    (Fin.cases first54_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.RelationCertificate
