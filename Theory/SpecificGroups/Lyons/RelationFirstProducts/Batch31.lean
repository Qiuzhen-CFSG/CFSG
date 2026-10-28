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
private theorem valid8 : checkValid m8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row0 :
    checkProductRow m136 m8 m137 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row1 :
    checkProductRow m136 m8 m137 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row2 :
    checkProductRow m136 m8 m137 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row3 :
    checkProductRow m136 m8 m137 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row4 :
    checkProductRow m136 m8 m137 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row5 :
    checkProductRow m136 m8 m137 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row6 :
    checkProductRow m136 m8 m137 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row7 :
    checkProductRow m136 m8 m137 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row8 :
    checkProductRow m136 m8 m137 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row9 :
    checkProductRow m136 m8 m137 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row10 :
    checkProductRow m136 m8 m137 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row11 :
    checkProductRow m136 m8 m137 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row12 :
    checkProductRow m136 m8 m137 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row13 :
    checkProductRow m136 m8 m137 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row14 :
    checkProductRow m136 m8 m137 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row15 :
    checkProductRow m136 m8 m137 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row16 :
    checkProductRow m136 m8 m137 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row17 :
    checkProductRow m136 m8 m137 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row18 :
    checkProductRow m136 m8 m137 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row19 :
    checkProductRow m136 m8 m137 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row20 :
    checkProductRow m136 m8 m137 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row21 :
    checkProductRow m136 m8 m137 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row22 :
    checkProductRow m136 m8 m137 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row23 :
    checkProductRow m136 m8 m137 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row24 :
    checkProductRow m136 m8 m137 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row25 :
    checkProductRow m136 m8 m137 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row26 :
    checkProductRow m136 m8 m137 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row27 :
    checkProductRow m136 m8 m137 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row28 :
    checkProductRow m136 m8 m137 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row29 :
    checkProductRow m136 m8 m137 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row30 :
    checkProductRow m136 m8 m137 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row31 :
    checkProductRow m136 m8 m137 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row32 :
    checkProductRow m136 m8 m137 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row33 :
    checkProductRow m136 m8 m137 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row34 :
    checkProductRow m136 m8 m137 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row35 :
    checkProductRow m136 m8 m137 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row36 :
    checkProductRow m136 m8 m137 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row37 :
    checkProductRow m136 m8 m137 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row38 :
    checkProductRow m136 m8 m137 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row39 :
    checkProductRow m136 m8 m137 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row40 :
    checkProductRow m136 m8 m137 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row41 :
    checkProductRow m136 m8 m137 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row42 :
    checkProductRow m136 m8 m137 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row43 :
    checkProductRow m136 m8 m137 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row44 :
    checkProductRow m136 m8 m137 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row45 :
    checkProductRow m136 m8 m137 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row46 :
    checkProductRow m136 m8 m137 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row47 :
    checkProductRow m136 m8 m137 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row48 :
    checkProductRow m136 m8 m137 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row49 :
    checkProductRow m136 m8 m137 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row50 :
    checkProductRow m136 m8 m137 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row51 :
    checkProductRow m136 m8 m137 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row52 :
    checkProductRow m136 m8 m137 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row53 :
    checkProductRow m136 m8 m137 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row54 :
    checkProductRow m136 m8 m137 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row55 :
    checkProductRow m136 m8 m137 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row56 :
    checkProductRow m136 m8 m137 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row57 :
    checkProductRow m136 m8 m137 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row58 :
    checkProductRow m136 m8 m137 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row59 :
    checkProductRow m136 m8 m137 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row60 :
    checkProductRow m136 m8 m137 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row61 :
    checkProductRow m136 m8 m137 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row62 :
    checkProductRow m136 m8 m137 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row63 :
    checkProductRow m136 m8 m137 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row64 :
    checkProductRow m136 m8 m137 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row65 :
    checkProductRow m136 m8 m137 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row66 :
    checkProductRow m136 m8 m137 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row67 :
    checkProductRow m136 m8 m137 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row68 :
    checkProductRow m136 m8 m137 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row69 :
    checkProductRow m136 m8 m137 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row70 :
    checkProductRow m136 m8 m137 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row71 :
    checkProductRow m136 m8 m137 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row72 :
    checkProductRow m136 m8 m137 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row73 :
    checkProductRow m136 m8 m137 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row74 :
    checkProductRow m136 m8 m137 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row75 :
    checkProductRow m136 m8 m137 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row76 :
    checkProductRow m136 m8 m137 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row77 :
    checkProductRow m136 m8 m137 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row78 :
    checkProductRow m136 m8 m137 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row79 :
    checkProductRow m136 m8 m137 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row80 :
    checkProductRow m136 m8 m137 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row81 :
    checkProductRow m136 m8 m137 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row82 :
    checkProductRow m136 m8 m137 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row83 :
    checkProductRow m136 m8 m137 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row84 :
    checkProductRow m136 m8 m137 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row85 :
    checkProductRow m136 m8 m137 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row86 :
    checkProductRow m136 m8 m137 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row87 :
    checkProductRow m136 m8 m137 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row88 :
    checkProductRow m136 m8 m137 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row89 :
    checkProductRow m136 m8 m137 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row90 :
    checkProductRow m136 m8 m137 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row91 :
    checkProductRow m136 m8 m137 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row92 :
    checkProductRow m136 m8 m137 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row93 :
    checkProductRow m136 m8 m137 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row94 :
    checkProductRow m136 m8 m137 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row95 :
    checkProductRow m136 m8 m137 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row96 :
    checkProductRow m136 m8 m137 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row97 :
    checkProductRow m136 m8 m137 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row98 :
    checkProductRow m136 m8 m137 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row99 :
    checkProductRow m136 m8 m137 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row100 :
    checkProductRow m136 m8 m137 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row101 :
    checkProductRow m136 m8 m137 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row102 :
    checkProductRow m136 m8 m137 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row103 :
    checkProductRow m136 m8 m137 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row104 :
    checkProductRow m136 m8 m137 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row105 :
    checkProductRow m136 m8 m137 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row106 :
    checkProductRow m136 m8 m137 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row107 :
    checkProductRow m136 m8 m137 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row108 :
    checkProductRow m136 m8 m137 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row109 :
    checkProductRow m136 m8 m137 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first31_row110 :
    checkProductRow m136 m8 m137 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product31 :
    decode (matrixRows 136) * decode (matrixRows 8) = decode (matrixRows 137) :=
  product_of_checked_rows m136 m8 m137 valid8
    (Fin.cases first31_row0
    (Fin.cases first31_row1
    (Fin.cases first31_row2
    (Fin.cases first31_row3
    (Fin.cases first31_row4
    (Fin.cases first31_row5
    (Fin.cases first31_row6
    (Fin.cases first31_row7
    (Fin.cases first31_row8
    (Fin.cases first31_row9
    (Fin.cases first31_row10
    (Fin.cases first31_row11
    (Fin.cases first31_row12
    (Fin.cases first31_row13
    (Fin.cases first31_row14
    (Fin.cases first31_row15
    (Fin.cases first31_row16
    (Fin.cases first31_row17
    (Fin.cases first31_row18
    (Fin.cases first31_row19
    (Fin.cases first31_row20
    (Fin.cases first31_row21
    (Fin.cases first31_row22
    (Fin.cases first31_row23
    (Fin.cases first31_row24
    (Fin.cases first31_row25
    (Fin.cases first31_row26
    (Fin.cases first31_row27
    (Fin.cases first31_row28
    (Fin.cases first31_row29
    (Fin.cases first31_row30
    (Fin.cases first31_row31
    (Fin.cases first31_row32
    (Fin.cases first31_row33
    (Fin.cases first31_row34
    (Fin.cases first31_row35
    (Fin.cases first31_row36
    (Fin.cases first31_row37
    (Fin.cases first31_row38
    (Fin.cases first31_row39
    (Fin.cases first31_row40
    (Fin.cases first31_row41
    (Fin.cases first31_row42
    (Fin.cases first31_row43
    (Fin.cases first31_row44
    (Fin.cases first31_row45
    (Fin.cases first31_row46
    (Fin.cases first31_row47
    (Fin.cases first31_row48
    (Fin.cases first31_row49
    (Fin.cases first31_row50
    (Fin.cases first31_row51
    (Fin.cases first31_row52
    (Fin.cases first31_row53
    (Fin.cases first31_row54
    (Fin.cases first31_row55
    (Fin.cases first31_row56
    (Fin.cases first31_row57
    (Fin.cases first31_row58
    (Fin.cases first31_row59
    (Fin.cases first31_row60
    (Fin.cases first31_row61
    (Fin.cases first31_row62
    (Fin.cases first31_row63
    (Fin.cases first31_row64
    (Fin.cases first31_row65
    (Fin.cases first31_row66
    (Fin.cases first31_row67
    (Fin.cases first31_row68
    (Fin.cases first31_row69
    (Fin.cases first31_row70
    (Fin.cases first31_row71
    (Fin.cases first31_row72
    (Fin.cases first31_row73
    (Fin.cases first31_row74
    (Fin.cases first31_row75
    (Fin.cases first31_row76
    (Fin.cases first31_row77
    (Fin.cases first31_row78
    (Fin.cases first31_row79
    (Fin.cases first31_row80
    (Fin.cases first31_row81
    (Fin.cases first31_row82
    (Fin.cases first31_row83
    (Fin.cases first31_row84
    (Fin.cases first31_row85
    (Fin.cases first31_row86
    (Fin.cases first31_row87
    (Fin.cases first31_row88
    (Fin.cases first31_row89
    (Fin.cases first31_row90
    (Fin.cases first31_row91
    (Fin.cases first31_row92
    (Fin.cases first31_row93
    (Fin.cases first31_row94
    (Fin.cases first31_row95
    (Fin.cases first31_row96
    (Fin.cases first31_row97
    (Fin.cases first31_row98
    (Fin.cases first31_row99
    (Fin.cases first31_row100
    (Fin.cases first31_row101
    (Fin.cases first31_row102
    (Fin.cases first31_row103
    (Fin.cases first31_row104
    (Fin.cases first31_row105
    (Fin.cases first31_row106
    (Fin.cases first31_row107
    (Fin.cases first31_row108
    (Fin.cases first31_row109
    (Fin.cases first31_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid11 : checkValid m11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row0 :
    checkProductRow m137 m11 m138 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row1 :
    checkProductRow m137 m11 m138 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row2 :
    checkProductRow m137 m11 m138 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row3 :
    checkProductRow m137 m11 m138 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row4 :
    checkProductRow m137 m11 m138 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row5 :
    checkProductRow m137 m11 m138 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row6 :
    checkProductRow m137 m11 m138 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row7 :
    checkProductRow m137 m11 m138 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row8 :
    checkProductRow m137 m11 m138 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row9 :
    checkProductRow m137 m11 m138 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row10 :
    checkProductRow m137 m11 m138 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row11 :
    checkProductRow m137 m11 m138 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row12 :
    checkProductRow m137 m11 m138 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row13 :
    checkProductRow m137 m11 m138 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row14 :
    checkProductRow m137 m11 m138 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row15 :
    checkProductRow m137 m11 m138 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row16 :
    checkProductRow m137 m11 m138 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row17 :
    checkProductRow m137 m11 m138 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row18 :
    checkProductRow m137 m11 m138 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row19 :
    checkProductRow m137 m11 m138 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row20 :
    checkProductRow m137 m11 m138 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row21 :
    checkProductRow m137 m11 m138 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row22 :
    checkProductRow m137 m11 m138 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row23 :
    checkProductRow m137 m11 m138 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row24 :
    checkProductRow m137 m11 m138 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row25 :
    checkProductRow m137 m11 m138 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row26 :
    checkProductRow m137 m11 m138 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row27 :
    checkProductRow m137 m11 m138 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row28 :
    checkProductRow m137 m11 m138 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row29 :
    checkProductRow m137 m11 m138 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row30 :
    checkProductRow m137 m11 m138 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row31 :
    checkProductRow m137 m11 m138 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row32 :
    checkProductRow m137 m11 m138 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row33 :
    checkProductRow m137 m11 m138 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row34 :
    checkProductRow m137 m11 m138 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row35 :
    checkProductRow m137 m11 m138 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row36 :
    checkProductRow m137 m11 m138 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row37 :
    checkProductRow m137 m11 m138 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row38 :
    checkProductRow m137 m11 m138 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row39 :
    checkProductRow m137 m11 m138 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row40 :
    checkProductRow m137 m11 m138 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row41 :
    checkProductRow m137 m11 m138 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row42 :
    checkProductRow m137 m11 m138 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row43 :
    checkProductRow m137 m11 m138 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row44 :
    checkProductRow m137 m11 m138 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row45 :
    checkProductRow m137 m11 m138 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row46 :
    checkProductRow m137 m11 m138 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row47 :
    checkProductRow m137 m11 m138 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row48 :
    checkProductRow m137 m11 m138 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row49 :
    checkProductRow m137 m11 m138 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row50 :
    checkProductRow m137 m11 m138 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row51 :
    checkProductRow m137 m11 m138 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row52 :
    checkProductRow m137 m11 m138 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row53 :
    checkProductRow m137 m11 m138 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row54 :
    checkProductRow m137 m11 m138 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row55 :
    checkProductRow m137 m11 m138 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row56 :
    checkProductRow m137 m11 m138 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row57 :
    checkProductRow m137 m11 m138 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row58 :
    checkProductRow m137 m11 m138 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row59 :
    checkProductRow m137 m11 m138 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row60 :
    checkProductRow m137 m11 m138 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row61 :
    checkProductRow m137 m11 m138 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row62 :
    checkProductRow m137 m11 m138 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row63 :
    checkProductRow m137 m11 m138 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row64 :
    checkProductRow m137 m11 m138 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row65 :
    checkProductRow m137 m11 m138 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row66 :
    checkProductRow m137 m11 m138 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row67 :
    checkProductRow m137 m11 m138 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row68 :
    checkProductRow m137 m11 m138 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row69 :
    checkProductRow m137 m11 m138 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row70 :
    checkProductRow m137 m11 m138 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row71 :
    checkProductRow m137 m11 m138 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row72 :
    checkProductRow m137 m11 m138 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row73 :
    checkProductRow m137 m11 m138 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row74 :
    checkProductRow m137 m11 m138 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row75 :
    checkProductRow m137 m11 m138 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row76 :
    checkProductRow m137 m11 m138 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row77 :
    checkProductRow m137 m11 m138 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row78 :
    checkProductRow m137 m11 m138 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row79 :
    checkProductRow m137 m11 m138 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row80 :
    checkProductRow m137 m11 m138 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row81 :
    checkProductRow m137 m11 m138 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row82 :
    checkProductRow m137 m11 m138 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row83 :
    checkProductRow m137 m11 m138 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row84 :
    checkProductRow m137 m11 m138 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row85 :
    checkProductRow m137 m11 m138 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row86 :
    checkProductRow m137 m11 m138 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row87 :
    checkProductRow m137 m11 m138 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row88 :
    checkProductRow m137 m11 m138 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row89 :
    checkProductRow m137 m11 m138 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row90 :
    checkProductRow m137 m11 m138 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row91 :
    checkProductRow m137 m11 m138 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row92 :
    checkProductRow m137 m11 m138 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row93 :
    checkProductRow m137 m11 m138 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row94 :
    checkProductRow m137 m11 m138 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row95 :
    checkProductRow m137 m11 m138 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row96 :
    checkProductRow m137 m11 m138 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row97 :
    checkProductRow m137 m11 m138 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row98 :
    checkProductRow m137 m11 m138 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row99 :
    checkProductRow m137 m11 m138 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row100 :
    checkProductRow m137 m11 m138 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row101 :
    checkProductRow m137 m11 m138 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row102 :
    checkProductRow m137 m11 m138 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row103 :
    checkProductRow m137 m11 m138 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row104 :
    checkProductRow m137 m11 m138 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row105 :
    checkProductRow m137 m11 m138 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row106 :
    checkProductRow m137 m11 m138 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row107 :
    checkProductRow m137 m11 m138 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row108 :
    checkProductRow m137 m11 m138 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row109 :
    checkProductRow m137 m11 m138 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first32_row110 :
    checkProductRow m137 m11 m138 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product32 :
    decode (matrixRows 137) * decode (matrixRows 11) = decode (matrixRows 138) :=
  product_of_checked_rows m137 m11 m138 valid11
    (Fin.cases first32_row0
    (Fin.cases first32_row1
    (Fin.cases first32_row2
    (Fin.cases first32_row3
    (Fin.cases first32_row4
    (Fin.cases first32_row5
    (Fin.cases first32_row6
    (Fin.cases first32_row7
    (Fin.cases first32_row8
    (Fin.cases first32_row9
    (Fin.cases first32_row10
    (Fin.cases first32_row11
    (Fin.cases first32_row12
    (Fin.cases first32_row13
    (Fin.cases first32_row14
    (Fin.cases first32_row15
    (Fin.cases first32_row16
    (Fin.cases first32_row17
    (Fin.cases first32_row18
    (Fin.cases first32_row19
    (Fin.cases first32_row20
    (Fin.cases first32_row21
    (Fin.cases first32_row22
    (Fin.cases first32_row23
    (Fin.cases first32_row24
    (Fin.cases first32_row25
    (Fin.cases first32_row26
    (Fin.cases first32_row27
    (Fin.cases first32_row28
    (Fin.cases first32_row29
    (Fin.cases first32_row30
    (Fin.cases first32_row31
    (Fin.cases first32_row32
    (Fin.cases first32_row33
    (Fin.cases first32_row34
    (Fin.cases first32_row35
    (Fin.cases first32_row36
    (Fin.cases first32_row37
    (Fin.cases first32_row38
    (Fin.cases first32_row39
    (Fin.cases first32_row40
    (Fin.cases first32_row41
    (Fin.cases first32_row42
    (Fin.cases first32_row43
    (Fin.cases first32_row44
    (Fin.cases first32_row45
    (Fin.cases first32_row46
    (Fin.cases first32_row47
    (Fin.cases first32_row48
    (Fin.cases first32_row49
    (Fin.cases first32_row50
    (Fin.cases first32_row51
    (Fin.cases first32_row52
    (Fin.cases first32_row53
    (Fin.cases first32_row54
    (Fin.cases first32_row55
    (Fin.cases first32_row56
    (Fin.cases first32_row57
    (Fin.cases first32_row58
    (Fin.cases first32_row59
    (Fin.cases first32_row60
    (Fin.cases first32_row61
    (Fin.cases first32_row62
    (Fin.cases first32_row63
    (Fin.cases first32_row64
    (Fin.cases first32_row65
    (Fin.cases first32_row66
    (Fin.cases first32_row67
    (Fin.cases first32_row68
    (Fin.cases first32_row69
    (Fin.cases first32_row70
    (Fin.cases first32_row71
    (Fin.cases first32_row72
    (Fin.cases first32_row73
    (Fin.cases first32_row74
    (Fin.cases first32_row75
    (Fin.cases first32_row76
    (Fin.cases first32_row77
    (Fin.cases first32_row78
    (Fin.cases first32_row79
    (Fin.cases first32_row80
    (Fin.cases first32_row81
    (Fin.cases first32_row82
    (Fin.cases first32_row83
    (Fin.cases first32_row84
    (Fin.cases first32_row85
    (Fin.cases first32_row86
    (Fin.cases first32_row87
    (Fin.cases first32_row88
    (Fin.cases first32_row89
    (Fin.cases first32_row90
    (Fin.cases first32_row91
    (Fin.cases first32_row92
    (Fin.cases first32_row93
    (Fin.cases first32_row94
    (Fin.cases first32_row95
    (Fin.cases first32_row96
    (Fin.cases first32_row97
    (Fin.cases first32_row98
    (Fin.cases first32_row99
    (Fin.cases first32_row100
    (Fin.cases first32_row101
    (Fin.cases first32_row102
    (Fin.cases first32_row103
    (Fin.cases first32_row104
    (Fin.cases first32_row105
    (Fin.cases first32_row106
    (Fin.cases first32_row107
    (Fin.cases first32_row108
    (Fin.cases first32_row109
    (Fin.cases first32_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid85 : checkValid m85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row0 :
    checkProductRow m138 m85 m139 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row1 :
    checkProductRow m138 m85 m139 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row2 :
    checkProductRow m138 m85 m139 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row3 :
    checkProductRow m138 m85 m139 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row4 :
    checkProductRow m138 m85 m139 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row5 :
    checkProductRow m138 m85 m139 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row6 :
    checkProductRow m138 m85 m139 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row7 :
    checkProductRow m138 m85 m139 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row8 :
    checkProductRow m138 m85 m139 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row9 :
    checkProductRow m138 m85 m139 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row10 :
    checkProductRow m138 m85 m139 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row11 :
    checkProductRow m138 m85 m139 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row12 :
    checkProductRow m138 m85 m139 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row13 :
    checkProductRow m138 m85 m139 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row14 :
    checkProductRow m138 m85 m139 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row15 :
    checkProductRow m138 m85 m139 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row16 :
    checkProductRow m138 m85 m139 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row17 :
    checkProductRow m138 m85 m139 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row18 :
    checkProductRow m138 m85 m139 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row19 :
    checkProductRow m138 m85 m139 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row20 :
    checkProductRow m138 m85 m139 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row21 :
    checkProductRow m138 m85 m139 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row22 :
    checkProductRow m138 m85 m139 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row23 :
    checkProductRow m138 m85 m139 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row24 :
    checkProductRow m138 m85 m139 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row25 :
    checkProductRow m138 m85 m139 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row26 :
    checkProductRow m138 m85 m139 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row27 :
    checkProductRow m138 m85 m139 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row28 :
    checkProductRow m138 m85 m139 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row29 :
    checkProductRow m138 m85 m139 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row30 :
    checkProductRow m138 m85 m139 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row31 :
    checkProductRow m138 m85 m139 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row32 :
    checkProductRow m138 m85 m139 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row33 :
    checkProductRow m138 m85 m139 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row34 :
    checkProductRow m138 m85 m139 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row35 :
    checkProductRow m138 m85 m139 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row36 :
    checkProductRow m138 m85 m139 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row37 :
    checkProductRow m138 m85 m139 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row38 :
    checkProductRow m138 m85 m139 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row39 :
    checkProductRow m138 m85 m139 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row40 :
    checkProductRow m138 m85 m139 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row41 :
    checkProductRow m138 m85 m139 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row42 :
    checkProductRow m138 m85 m139 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row43 :
    checkProductRow m138 m85 m139 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row44 :
    checkProductRow m138 m85 m139 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row45 :
    checkProductRow m138 m85 m139 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row46 :
    checkProductRow m138 m85 m139 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row47 :
    checkProductRow m138 m85 m139 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row48 :
    checkProductRow m138 m85 m139 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row49 :
    checkProductRow m138 m85 m139 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row50 :
    checkProductRow m138 m85 m139 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row51 :
    checkProductRow m138 m85 m139 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row52 :
    checkProductRow m138 m85 m139 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row53 :
    checkProductRow m138 m85 m139 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row54 :
    checkProductRow m138 m85 m139 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row55 :
    checkProductRow m138 m85 m139 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row56 :
    checkProductRow m138 m85 m139 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row57 :
    checkProductRow m138 m85 m139 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row58 :
    checkProductRow m138 m85 m139 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row59 :
    checkProductRow m138 m85 m139 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row60 :
    checkProductRow m138 m85 m139 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row61 :
    checkProductRow m138 m85 m139 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row62 :
    checkProductRow m138 m85 m139 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row63 :
    checkProductRow m138 m85 m139 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row64 :
    checkProductRow m138 m85 m139 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row65 :
    checkProductRow m138 m85 m139 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row66 :
    checkProductRow m138 m85 m139 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row67 :
    checkProductRow m138 m85 m139 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row68 :
    checkProductRow m138 m85 m139 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row69 :
    checkProductRow m138 m85 m139 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row70 :
    checkProductRow m138 m85 m139 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row71 :
    checkProductRow m138 m85 m139 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row72 :
    checkProductRow m138 m85 m139 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row73 :
    checkProductRow m138 m85 m139 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row74 :
    checkProductRow m138 m85 m139 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row75 :
    checkProductRow m138 m85 m139 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row76 :
    checkProductRow m138 m85 m139 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row77 :
    checkProductRow m138 m85 m139 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row78 :
    checkProductRow m138 m85 m139 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row79 :
    checkProductRow m138 m85 m139 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row80 :
    checkProductRow m138 m85 m139 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row81 :
    checkProductRow m138 m85 m139 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row82 :
    checkProductRow m138 m85 m139 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row83 :
    checkProductRow m138 m85 m139 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row84 :
    checkProductRow m138 m85 m139 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row85 :
    checkProductRow m138 m85 m139 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row86 :
    checkProductRow m138 m85 m139 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row87 :
    checkProductRow m138 m85 m139 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row88 :
    checkProductRow m138 m85 m139 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row89 :
    checkProductRow m138 m85 m139 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row90 :
    checkProductRow m138 m85 m139 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row91 :
    checkProductRow m138 m85 m139 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row92 :
    checkProductRow m138 m85 m139 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row93 :
    checkProductRow m138 m85 m139 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row94 :
    checkProductRow m138 m85 m139 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row95 :
    checkProductRow m138 m85 m139 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row96 :
    checkProductRow m138 m85 m139 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row97 :
    checkProductRow m138 m85 m139 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row98 :
    checkProductRow m138 m85 m139 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row99 :
    checkProductRow m138 m85 m139 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row100 :
    checkProductRow m138 m85 m139 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row101 :
    checkProductRow m138 m85 m139 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row102 :
    checkProductRow m138 m85 m139 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row103 :
    checkProductRow m138 m85 m139 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row104 :
    checkProductRow m138 m85 m139 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row105 :
    checkProductRow m138 m85 m139 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row106 :
    checkProductRow m138 m85 m139 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row107 :
    checkProductRow m138 m85 m139 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row108 :
    checkProductRow m138 m85 m139 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row109 :
    checkProductRow m138 m85 m139 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first33_row110 :
    checkProductRow m138 m85 m139 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product33 :
    decode (matrixRows 138) * decode (matrixRows 85) = decode (matrixRows 139) :=
  product_of_checked_rows m138 m85 m139 valid85
    (Fin.cases first33_row0
    (Fin.cases first33_row1
    (Fin.cases first33_row2
    (Fin.cases first33_row3
    (Fin.cases first33_row4
    (Fin.cases first33_row5
    (Fin.cases first33_row6
    (Fin.cases first33_row7
    (Fin.cases first33_row8
    (Fin.cases first33_row9
    (Fin.cases first33_row10
    (Fin.cases first33_row11
    (Fin.cases first33_row12
    (Fin.cases first33_row13
    (Fin.cases first33_row14
    (Fin.cases first33_row15
    (Fin.cases first33_row16
    (Fin.cases first33_row17
    (Fin.cases first33_row18
    (Fin.cases first33_row19
    (Fin.cases first33_row20
    (Fin.cases first33_row21
    (Fin.cases first33_row22
    (Fin.cases first33_row23
    (Fin.cases first33_row24
    (Fin.cases first33_row25
    (Fin.cases first33_row26
    (Fin.cases first33_row27
    (Fin.cases first33_row28
    (Fin.cases first33_row29
    (Fin.cases first33_row30
    (Fin.cases first33_row31
    (Fin.cases first33_row32
    (Fin.cases first33_row33
    (Fin.cases first33_row34
    (Fin.cases first33_row35
    (Fin.cases first33_row36
    (Fin.cases first33_row37
    (Fin.cases first33_row38
    (Fin.cases first33_row39
    (Fin.cases first33_row40
    (Fin.cases first33_row41
    (Fin.cases first33_row42
    (Fin.cases first33_row43
    (Fin.cases first33_row44
    (Fin.cases first33_row45
    (Fin.cases first33_row46
    (Fin.cases first33_row47
    (Fin.cases first33_row48
    (Fin.cases first33_row49
    (Fin.cases first33_row50
    (Fin.cases first33_row51
    (Fin.cases first33_row52
    (Fin.cases first33_row53
    (Fin.cases first33_row54
    (Fin.cases first33_row55
    (Fin.cases first33_row56
    (Fin.cases first33_row57
    (Fin.cases first33_row58
    (Fin.cases first33_row59
    (Fin.cases first33_row60
    (Fin.cases first33_row61
    (Fin.cases first33_row62
    (Fin.cases first33_row63
    (Fin.cases first33_row64
    (Fin.cases first33_row65
    (Fin.cases first33_row66
    (Fin.cases first33_row67
    (Fin.cases first33_row68
    (Fin.cases first33_row69
    (Fin.cases first33_row70
    (Fin.cases first33_row71
    (Fin.cases first33_row72
    (Fin.cases first33_row73
    (Fin.cases first33_row74
    (Fin.cases first33_row75
    (Fin.cases first33_row76
    (Fin.cases first33_row77
    (Fin.cases first33_row78
    (Fin.cases first33_row79
    (Fin.cases first33_row80
    (Fin.cases first33_row81
    (Fin.cases first33_row82
    (Fin.cases first33_row83
    (Fin.cases first33_row84
    (Fin.cases first33_row85
    (Fin.cases first33_row86
    (Fin.cases first33_row87
    (Fin.cases first33_row88
    (Fin.cases first33_row89
    (Fin.cases first33_row90
    (Fin.cases first33_row91
    (Fin.cases first33_row92
    (Fin.cases first33_row93
    (Fin.cases first33_row94
    (Fin.cases first33_row95
    (Fin.cases first33_row96
    (Fin.cases first33_row97
    (Fin.cases first33_row98
    (Fin.cases first33_row99
    (Fin.cases first33_row100
    (Fin.cases first33_row101
    (Fin.cases first33_row102
    (Fin.cases first33_row103
    (Fin.cases first33_row104
    (Fin.cases first33_row105
    (Fin.cases first33_row106
    (Fin.cases first33_row107
    (Fin.cases first33_row108
    (Fin.cases first33_row109
    (Fin.cases first33_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid86 : checkValid m86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row0 :
    checkProductRow m139 m86 m140 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row1 :
    checkProductRow m139 m86 m140 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row2 :
    checkProductRow m139 m86 m140 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row3 :
    checkProductRow m139 m86 m140 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row4 :
    checkProductRow m139 m86 m140 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row5 :
    checkProductRow m139 m86 m140 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row6 :
    checkProductRow m139 m86 m140 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row7 :
    checkProductRow m139 m86 m140 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row8 :
    checkProductRow m139 m86 m140 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row9 :
    checkProductRow m139 m86 m140 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row10 :
    checkProductRow m139 m86 m140 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row11 :
    checkProductRow m139 m86 m140 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row12 :
    checkProductRow m139 m86 m140 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row13 :
    checkProductRow m139 m86 m140 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row14 :
    checkProductRow m139 m86 m140 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row15 :
    checkProductRow m139 m86 m140 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row16 :
    checkProductRow m139 m86 m140 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row17 :
    checkProductRow m139 m86 m140 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row18 :
    checkProductRow m139 m86 m140 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row19 :
    checkProductRow m139 m86 m140 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row20 :
    checkProductRow m139 m86 m140 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row21 :
    checkProductRow m139 m86 m140 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row22 :
    checkProductRow m139 m86 m140 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row23 :
    checkProductRow m139 m86 m140 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row24 :
    checkProductRow m139 m86 m140 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row25 :
    checkProductRow m139 m86 m140 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row26 :
    checkProductRow m139 m86 m140 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row27 :
    checkProductRow m139 m86 m140 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row28 :
    checkProductRow m139 m86 m140 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row29 :
    checkProductRow m139 m86 m140 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row30 :
    checkProductRow m139 m86 m140 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row31 :
    checkProductRow m139 m86 m140 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row32 :
    checkProductRow m139 m86 m140 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row33 :
    checkProductRow m139 m86 m140 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row34 :
    checkProductRow m139 m86 m140 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row35 :
    checkProductRow m139 m86 m140 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row36 :
    checkProductRow m139 m86 m140 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row37 :
    checkProductRow m139 m86 m140 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row38 :
    checkProductRow m139 m86 m140 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row39 :
    checkProductRow m139 m86 m140 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row40 :
    checkProductRow m139 m86 m140 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row41 :
    checkProductRow m139 m86 m140 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row42 :
    checkProductRow m139 m86 m140 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row43 :
    checkProductRow m139 m86 m140 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row44 :
    checkProductRow m139 m86 m140 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row45 :
    checkProductRow m139 m86 m140 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row46 :
    checkProductRow m139 m86 m140 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row47 :
    checkProductRow m139 m86 m140 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row48 :
    checkProductRow m139 m86 m140 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row49 :
    checkProductRow m139 m86 m140 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row50 :
    checkProductRow m139 m86 m140 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row51 :
    checkProductRow m139 m86 m140 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row52 :
    checkProductRow m139 m86 m140 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row53 :
    checkProductRow m139 m86 m140 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row54 :
    checkProductRow m139 m86 m140 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row55 :
    checkProductRow m139 m86 m140 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row56 :
    checkProductRow m139 m86 m140 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row57 :
    checkProductRow m139 m86 m140 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row58 :
    checkProductRow m139 m86 m140 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row59 :
    checkProductRow m139 m86 m140 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row60 :
    checkProductRow m139 m86 m140 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row61 :
    checkProductRow m139 m86 m140 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row62 :
    checkProductRow m139 m86 m140 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row63 :
    checkProductRow m139 m86 m140 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row64 :
    checkProductRow m139 m86 m140 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row65 :
    checkProductRow m139 m86 m140 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row66 :
    checkProductRow m139 m86 m140 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row67 :
    checkProductRow m139 m86 m140 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row68 :
    checkProductRow m139 m86 m140 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row69 :
    checkProductRow m139 m86 m140 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row70 :
    checkProductRow m139 m86 m140 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row71 :
    checkProductRow m139 m86 m140 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row72 :
    checkProductRow m139 m86 m140 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row73 :
    checkProductRow m139 m86 m140 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row74 :
    checkProductRow m139 m86 m140 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row75 :
    checkProductRow m139 m86 m140 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row76 :
    checkProductRow m139 m86 m140 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row77 :
    checkProductRow m139 m86 m140 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row78 :
    checkProductRow m139 m86 m140 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row79 :
    checkProductRow m139 m86 m140 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row80 :
    checkProductRow m139 m86 m140 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row81 :
    checkProductRow m139 m86 m140 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row82 :
    checkProductRow m139 m86 m140 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row83 :
    checkProductRow m139 m86 m140 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row84 :
    checkProductRow m139 m86 m140 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row85 :
    checkProductRow m139 m86 m140 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row86 :
    checkProductRow m139 m86 m140 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row87 :
    checkProductRow m139 m86 m140 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row88 :
    checkProductRow m139 m86 m140 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row89 :
    checkProductRow m139 m86 m140 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row90 :
    checkProductRow m139 m86 m140 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row91 :
    checkProductRow m139 m86 m140 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row92 :
    checkProductRow m139 m86 m140 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row93 :
    checkProductRow m139 m86 m140 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row94 :
    checkProductRow m139 m86 m140 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row95 :
    checkProductRow m139 m86 m140 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row96 :
    checkProductRow m139 m86 m140 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row97 :
    checkProductRow m139 m86 m140 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row98 :
    checkProductRow m139 m86 m140 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row99 :
    checkProductRow m139 m86 m140 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row100 :
    checkProductRow m139 m86 m140 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row101 :
    checkProductRow m139 m86 m140 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row102 :
    checkProductRow m139 m86 m140 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row103 :
    checkProductRow m139 m86 m140 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row104 :
    checkProductRow m139 m86 m140 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row105 :
    checkProductRow m139 m86 m140 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row106 :
    checkProductRow m139 m86 m140 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row107 :
    checkProductRow m139 m86 m140 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row108 :
    checkProductRow m139 m86 m140 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row109 :
    checkProductRow m139 m86 m140 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first34_row110 :
    checkProductRow m139 m86 m140 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product34 :
    decode (matrixRows 139) * decode (matrixRows 86) = decode (matrixRows 140) :=
  product_of_checked_rows m139 m86 m140 valid86
    (Fin.cases first34_row0
    (Fin.cases first34_row1
    (Fin.cases first34_row2
    (Fin.cases first34_row3
    (Fin.cases first34_row4
    (Fin.cases first34_row5
    (Fin.cases first34_row6
    (Fin.cases first34_row7
    (Fin.cases first34_row8
    (Fin.cases first34_row9
    (Fin.cases first34_row10
    (Fin.cases first34_row11
    (Fin.cases first34_row12
    (Fin.cases first34_row13
    (Fin.cases first34_row14
    (Fin.cases first34_row15
    (Fin.cases first34_row16
    (Fin.cases first34_row17
    (Fin.cases first34_row18
    (Fin.cases first34_row19
    (Fin.cases first34_row20
    (Fin.cases first34_row21
    (Fin.cases first34_row22
    (Fin.cases first34_row23
    (Fin.cases first34_row24
    (Fin.cases first34_row25
    (Fin.cases first34_row26
    (Fin.cases first34_row27
    (Fin.cases first34_row28
    (Fin.cases first34_row29
    (Fin.cases first34_row30
    (Fin.cases first34_row31
    (Fin.cases first34_row32
    (Fin.cases first34_row33
    (Fin.cases first34_row34
    (Fin.cases first34_row35
    (Fin.cases first34_row36
    (Fin.cases first34_row37
    (Fin.cases first34_row38
    (Fin.cases first34_row39
    (Fin.cases first34_row40
    (Fin.cases first34_row41
    (Fin.cases first34_row42
    (Fin.cases first34_row43
    (Fin.cases first34_row44
    (Fin.cases first34_row45
    (Fin.cases first34_row46
    (Fin.cases first34_row47
    (Fin.cases first34_row48
    (Fin.cases first34_row49
    (Fin.cases first34_row50
    (Fin.cases first34_row51
    (Fin.cases first34_row52
    (Fin.cases first34_row53
    (Fin.cases first34_row54
    (Fin.cases first34_row55
    (Fin.cases first34_row56
    (Fin.cases first34_row57
    (Fin.cases first34_row58
    (Fin.cases first34_row59
    (Fin.cases first34_row60
    (Fin.cases first34_row61
    (Fin.cases first34_row62
    (Fin.cases first34_row63
    (Fin.cases first34_row64
    (Fin.cases first34_row65
    (Fin.cases first34_row66
    (Fin.cases first34_row67
    (Fin.cases first34_row68
    (Fin.cases first34_row69
    (Fin.cases first34_row70
    (Fin.cases first34_row71
    (Fin.cases first34_row72
    (Fin.cases first34_row73
    (Fin.cases first34_row74
    (Fin.cases first34_row75
    (Fin.cases first34_row76
    (Fin.cases first34_row77
    (Fin.cases first34_row78
    (Fin.cases first34_row79
    (Fin.cases first34_row80
    (Fin.cases first34_row81
    (Fin.cases first34_row82
    (Fin.cases first34_row83
    (Fin.cases first34_row84
    (Fin.cases first34_row85
    (Fin.cases first34_row86
    (Fin.cases first34_row87
    (Fin.cases first34_row88
    (Fin.cases first34_row89
    (Fin.cases first34_row90
    (Fin.cases first34_row91
    (Fin.cases first34_row92
    (Fin.cases first34_row93
    (Fin.cases first34_row94
    (Fin.cases first34_row95
    (Fin.cases first34_row96
    (Fin.cases first34_row97
    (Fin.cases first34_row98
    (Fin.cases first34_row99
    (Fin.cases first34_row100
    (Fin.cases first34_row101
    (Fin.cases first34_row102
    (Fin.cases first34_row103
    (Fin.cases first34_row104
    (Fin.cases first34_row105
    (Fin.cases first34_row106
    (Fin.cases first34_row107
    (Fin.cases first34_row108
    (Fin.cases first34_row109
    (Fin.cases first34_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid87 : checkValid m87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row0 :
    checkProductRow m140 m87 m0 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row1 :
    checkProductRow m140 m87 m0 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row2 :
    checkProductRow m140 m87 m0 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row3 :
    checkProductRow m140 m87 m0 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row4 :
    checkProductRow m140 m87 m0 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row5 :
    checkProductRow m140 m87 m0 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row6 :
    checkProductRow m140 m87 m0 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row7 :
    checkProductRow m140 m87 m0 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row8 :
    checkProductRow m140 m87 m0 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row9 :
    checkProductRow m140 m87 m0 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row10 :
    checkProductRow m140 m87 m0 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row11 :
    checkProductRow m140 m87 m0 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row12 :
    checkProductRow m140 m87 m0 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row13 :
    checkProductRow m140 m87 m0 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row14 :
    checkProductRow m140 m87 m0 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row15 :
    checkProductRow m140 m87 m0 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row16 :
    checkProductRow m140 m87 m0 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row17 :
    checkProductRow m140 m87 m0 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row18 :
    checkProductRow m140 m87 m0 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row19 :
    checkProductRow m140 m87 m0 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row20 :
    checkProductRow m140 m87 m0 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row21 :
    checkProductRow m140 m87 m0 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row22 :
    checkProductRow m140 m87 m0 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row23 :
    checkProductRow m140 m87 m0 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row24 :
    checkProductRow m140 m87 m0 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row25 :
    checkProductRow m140 m87 m0 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row26 :
    checkProductRow m140 m87 m0 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row27 :
    checkProductRow m140 m87 m0 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row28 :
    checkProductRow m140 m87 m0 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row29 :
    checkProductRow m140 m87 m0 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row30 :
    checkProductRow m140 m87 m0 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row31 :
    checkProductRow m140 m87 m0 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row32 :
    checkProductRow m140 m87 m0 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row33 :
    checkProductRow m140 m87 m0 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row34 :
    checkProductRow m140 m87 m0 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row35 :
    checkProductRow m140 m87 m0 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row36 :
    checkProductRow m140 m87 m0 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row37 :
    checkProductRow m140 m87 m0 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row38 :
    checkProductRow m140 m87 m0 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row39 :
    checkProductRow m140 m87 m0 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row40 :
    checkProductRow m140 m87 m0 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row41 :
    checkProductRow m140 m87 m0 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row42 :
    checkProductRow m140 m87 m0 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row43 :
    checkProductRow m140 m87 m0 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row44 :
    checkProductRow m140 m87 m0 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row45 :
    checkProductRow m140 m87 m0 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row46 :
    checkProductRow m140 m87 m0 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row47 :
    checkProductRow m140 m87 m0 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row48 :
    checkProductRow m140 m87 m0 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row49 :
    checkProductRow m140 m87 m0 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row50 :
    checkProductRow m140 m87 m0 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row51 :
    checkProductRow m140 m87 m0 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row52 :
    checkProductRow m140 m87 m0 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row53 :
    checkProductRow m140 m87 m0 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row54 :
    checkProductRow m140 m87 m0 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row55 :
    checkProductRow m140 m87 m0 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row56 :
    checkProductRow m140 m87 m0 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row57 :
    checkProductRow m140 m87 m0 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row58 :
    checkProductRow m140 m87 m0 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row59 :
    checkProductRow m140 m87 m0 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row60 :
    checkProductRow m140 m87 m0 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row61 :
    checkProductRow m140 m87 m0 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row62 :
    checkProductRow m140 m87 m0 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row63 :
    checkProductRow m140 m87 m0 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row64 :
    checkProductRow m140 m87 m0 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row65 :
    checkProductRow m140 m87 m0 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row66 :
    checkProductRow m140 m87 m0 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row67 :
    checkProductRow m140 m87 m0 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row68 :
    checkProductRow m140 m87 m0 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row69 :
    checkProductRow m140 m87 m0 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row70 :
    checkProductRow m140 m87 m0 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row71 :
    checkProductRow m140 m87 m0 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row72 :
    checkProductRow m140 m87 m0 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row73 :
    checkProductRow m140 m87 m0 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row74 :
    checkProductRow m140 m87 m0 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row75 :
    checkProductRow m140 m87 m0 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row76 :
    checkProductRow m140 m87 m0 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row77 :
    checkProductRow m140 m87 m0 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row78 :
    checkProductRow m140 m87 m0 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row79 :
    checkProductRow m140 m87 m0 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row80 :
    checkProductRow m140 m87 m0 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row81 :
    checkProductRow m140 m87 m0 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row82 :
    checkProductRow m140 m87 m0 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row83 :
    checkProductRow m140 m87 m0 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row84 :
    checkProductRow m140 m87 m0 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row85 :
    checkProductRow m140 m87 m0 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row86 :
    checkProductRow m140 m87 m0 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row87 :
    checkProductRow m140 m87 m0 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row88 :
    checkProductRow m140 m87 m0 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row89 :
    checkProductRow m140 m87 m0 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row90 :
    checkProductRow m140 m87 m0 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row91 :
    checkProductRow m140 m87 m0 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row92 :
    checkProductRow m140 m87 m0 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row93 :
    checkProductRow m140 m87 m0 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row94 :
    checkProductRow m140 m87 m0 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row95 :
    checkProductRow m140 m87 m0 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row96 :
    checkProductRow m140 m87 m0 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row97 :
    checkProductRow m140 m87 m0 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row98 :
    checkProductRow m140 m87 m0 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row99 :
    checkProductRow m140 m87 m0 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row100 :
    checkProductRow m140 m87 m0 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row101 :
    checkProductRow m140 m87 m0 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row102 :
    checkProductRow m140 m87 m0 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row103 :
    checkProductRow m140 m87 m0 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row104 :
    checkProductRow m140 m87 m0 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row105 :
    checkProductRow m140 m87 m0 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row106 :
    checkProductRow m140 m87 m0 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row107 :
    checkProductRow m140 m87 m0 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row108 :
    checkProductRow m140 m87 m0 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row109 :
    checkProductRow m140 m87 m0 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first35_row110 :
    checkProductRow m140 m87 m0 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product35 :
    decode (matrixRows 140) * decode (matrixRows 87) = decode (matrixRows 0) :=
  product_of_checked_rows m140 m87 m0 valid87
    (Fin.cases first35_row0
    (Fin.cases first35_row1
    (Fin.cases first35_row2
    (Fin.cases first35_row3
    (Fin.cases first35_row4
    (Fin.cases first35_row5
    (Fin.cases first35_row6
    (Fin.cases first35_row7
    (Fin.cases first35_row8
    (Fin.cases first35_row9
    (Fin.cases first35_row10
    (Fin.cases first35_row11
    (Fin.cases first35_row12
    (Fin.cases first35_row13
    (Fin.cases first35_row14
    (Fin.cases first35_row15
    (Fin.cases first35_row16
    (Fin.cases first35_row17
    (Fin.cases first35_row18
    (Fin.cases first35_row19
    (Fin.cases first35_row20
    (Fin.cases first35_row21
    (Fin.cases first35_row22
    (Fin.cases first35_row23
    (Fin.cases first35_row24
    (Fin.cases first35_row25
    (Fin.cases first35_row26
    (Fin.cases first35_row27
    (Fin.cases first35_row28
    (Fin.cases first35_row29
    (Fin.cases first35_row30
    (Fin.cases first35_row31
    (Fin.cases first35_row32
    (Fin.cases first35_row33
    (Fin.cases first35_row34
    (Fin.cases first35_row35
    (Fin.cases first35_row36
    (Fin.cases first35_row37
    (Fin.cases first35_row38
    (Fin.cases first35_row39
    (Fin.cases first35_row40
    (Fin.cases first35_row41
    (Fin.cases first35_row42
    (Fin.cases first35_row43
    (Fin.cases first35_row44
    (Fin.cases first35_row45
    (Fin.cases first35_row46
    (Fin.cases first35_row47
    (Fin.cases first35_row48
    (Fin.cases first35_row49
    (Fin.cases first35_row50
    (Fin.cases first35_row51
    (Fin.cases first35_row52
    (Fin.cases first35_row53
    (Fin.cases first35_row54
    (Fin.cases first35_row55
    (Fin.cases first35_row56
    (Fin.cases first35_row57
    (Fin.cases first35_row58
    (Fin.cases first35_row59
    (Fin.cases first35_row60
    (Fin.cases first35_row61
    (Fin.cases first35_row62
    (Fin.cases first35_row63
    (Fin.cases first35_row64
    (Fin.cases first35_row65
    (Fin.cases first35_row66
    (Fin.cases first35_row67
    (Fin.cases first35_row68
    (Fin.cases first35_row69
    (Fin.cases first35_row70
    (Fin.cases first35_row71
    (Fin.cases first35_row72
    (Fin.cases first35_row73
    (Fin.cases first35_row74
    (Fin.cases first35_row75
    (Fin.cases first35_row76
    (Fin.cases first35_row77
    (Fin.cases first35_row78
    (Fin.cases first35_row79
    (Fin.cases first35_row80
    (Fin.cases first35_row81
    (Fin.cases first35_row82
    (Fin.cases first35_row83
    (Fin.cases first35_row84
    (Fin.cases first35_row85
    (Fin.cases first35_row86
    (Fin.cases first35_row87
    (Fin.cases first35_row88
    (Fin.cases first35_row89
    (Fin.cases first35_row90
    (Fin.cases first35_row91
    (Fin.cases first35_row92
    (Fin.cases first35_row93
    (Fin.cases first35_row94
    (Fin.cases first35_row95
    (Fin.cases first35_row96
    (Fin.cases first35_row97
    (Fin.cases first35_row98
    (Fin.cases first35_row99
    (Fin.cases first35_row100
    (Fin.cases first35_row101
    (Fin.cases first35_row102
    (Fin.cases first35_row103
    (Fin.cases first35_row104
    (Fin.cases first35_row105
    (Fin.cases first35_row106
    (Fin.cases first35_row107
    (Fin.cases first35_row108
    (Fin.cases first35_row109
    (Fin.cases first35_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid88 : checkValid m88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row0 :
    checkProductRow m77 m88 m141 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row1 :
    checkProductRow m77 m88 m141 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row2 :
    checkProductRow m77 m88 m141 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row3 :
    checkProductRow m77 m88 m141 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row4 :
    checkProductRow m77 m88 m141 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row5 :
    checkProductRow m77 m88 m141 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row6 :
    checkProductRow m77 m88 m141 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row7 :
    checkProductRow m77 m88 m141 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row8 :
    checkProductRow m77 m88 m141 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row9 :
    checkProductRow m77 m88 m141 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row10 :
    checkProductRow m77 m88 m141 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row11 :
    checkProductRow m77 m88 m141 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row12 :
    checkProductRow m77 m88 m141 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row13 :
    checkProductRow m77 m88 m141 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row14 :
    checkProductRow m77 m88 m141 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row15 :
    checkProductRow m77 m88 m141 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row16 :
    checkProductRow m77 m88 m141 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row17 :
    checkProductRow m77 m88 m141 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row18 :
    checkProductRow m77 m88 m141 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row19 :
    checkProductRow m77 m88 m141 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row20 :
    checkProductRow m77 m88 m141 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row21 :
    checkProductRow m77 m88 m141 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row22 :
    checkProductRow m77 m88 m141 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row23 :
    checkProductRow m77 m88 m141 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row24 :
    checkProductRow m77 m88 m141 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row25 :
    checkProductRow m77 m88 m141 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row26 :
    checkProductRow m77 m88 m141 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row27 :
    checkProductRow m77 m88 m141 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row28 :
    checkProductRow m77 m88 m141 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row29 :
    checkProductRow m77 m88 m141 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row30 :
    checkProductRow m77 m88 m141 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row31 :
    checkProductRow m77 m88 m141 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row32 :
    checkProductRow m77 m88 m141 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row33 :
    checkProductRow m77 m88 m141 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row34 :
    checkProductRow m77 m88 m141 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row35 :
    checkProductRow m77 m88 m141 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row36 :
    checkProductRow m77 m88 m141 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row37 :
    checkProductRow m77 m88 m141 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row38 :
    checkProductRow m77 m88 m141 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row39 :
    checkProductRow m77 m88 m141 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row40 :
    checkProductRow m77 m88 m141 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row41 :
    checkProductRow m77 m88 m141 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row42 :
    checkProductRow m77 m88 m141 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row43 :
    checkProductRow m77 m88 m141 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row44 :
    checkProductRow m77 m88 m141 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row45 :
    checkProductRow m77 m88 m141 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row46 :
    checkProductRow m77 m88 m141 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row47 :
    checkProductRow m77 m88 m141 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row48 :
    checkProductRow m77 m88 m141 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row49 :
    checkProductRow m77 m88 m141 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row50 :
    checkProductRow m77 m88 m141 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row51 :
    checkProductRow m77 m88 m141 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row52 :
    checkProductRow m77 m88 m141 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row53 :
    checkProductRow m77 m88 m141 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row54 :
    checkProductRow m77 m88 m141 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row55 :
    checkProductRow m77 m88 m141 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row56 :
    checkProductRow m77 m88 m141 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row57 :
    checkProductRow m77 m88 m141 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row58 :
    checkProductRow m77 m88 m141 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row59 :
    checkProductRow m77 m88 m141 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row60 :
    checkProductRow m77 m88 m141 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row61 :
    checkProductRow m77 m88 m141 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row62 :
    checkProductRow m77 m88 m141 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row63 :
    checkProductRow m77 m88 m141 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row64 :
    checkProductRow m77 m88 m141 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row65 :
    checkProductRow m77 m88 m141 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row66 :
    checkProductRow m77 m88 m141 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row67 :
    checkProductRow m77 m88 m141 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row68 :
    checkProductRow m77 m88 m141 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row69 :
    checkProductRow m77 m88 m141 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row70 :
    checkProductRow m77 m88 m141 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row71 :
    checkProductRow m77 m88 m141 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row72 :
    checkProductRow m77 m88 m141 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row73 :
    checkProductRow m77 m88 m141 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row74 :
    checkProductRow m77 m88 m141 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row75 :
    checkProductRow m77 m88 m141 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row76 :
    checkProductRow m77 m88 m141 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row77 :
    checkProductRow m77 m88 m141 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row78 :
    checkProductRow m77 m88 m141 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row79 :
    checkProductRow m77 m88 m141 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row80 :
    checkProductRow m77 m88 m141 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row81 :
    checkProductRow m77 m88 m141 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row82 :
    checkProductRow m77 m88 m141 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row83 :
    checkProductRow m77 m88 m141 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row84 :
    checkProductRow m77 m88 m141 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row85 :
    checkProductRow m77 m88 m141 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row86 :
    checkProductRow m77 m88 m141 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row87 :
    checkProductRow m77 m88 m141 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row88 :
    checkProductRow m77 m88 m141 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row89 :
    checkProductRow m77 m88 m141 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row90 :
    checkProductRow m77 m88 m141 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row91 :
    checkProductRow m77 m88 m141 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row92 :
    checkProductRow m77 m88 m141 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row93 :
    checkProductRow m77 m88 m141 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row94 :
    checkProductRow m77 m88 m141 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row95 :
    checkProductRow m77 m88 m141 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row96 :
    checkProductRow m77 m88 m141 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row97 :
    checkProductRow m77 m88 m141 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row98 :
    checkProductRow m77 m88 m141 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row99 :
    checkProductRow m77 m88 m141 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row100 :
    checkProductRow m77 m88 m141 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row101 :
    checkProductRow m77 m88 m141 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row102 :
    checkProductRow m77 m88 m141 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row103 :
    checkProductRow m77 m88 m141 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row104 :
    checkProductRow m77 m88 m141 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row105 :
    checkProductRow m77 m88 m141 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row106 :
    checkProductRow m77 m88 m141 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row107 :
    checkProductRow m77 m88 m141 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row108 :
    checkProductRow m77 m88 m141 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row109 :
    checkProductRow m77 m88 m141 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first36_row110 :
    checkProductRow m77 m88 m141 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product36 :
    decode (matrixRows 77) * decode (matrixRows 88) = decode (matrixRows 141) :=
  product_of_checked_rows m77 m88 m141 valid88
    (Fin.cases first36_row0
    (Fin.cases first36_row1
    (Fin.cases first36_row2
    (Fin.cases first36_row3
    (Fin.cases first36_row4
    (Fin.cases first36_row5
    (Fin.cases first36_row6
    (Fin.cases first36_row7
    (Fin.cases first36_row8
    (Fin.cases first36_row9
    (Fin.cases first36_row10
    (Fin.cases first36_row11
    (Fin.cases first36_row12
    (Fin.cases first36_row13
    (Fin.cases first36_row14
    (Fin.cases first36_row15
    (Fin.cases first36_row16
    (Fin.cases first36_row17
    (Fin.cases first36_row18
    (Fin.cases first36_row19
    (Fin.cases first36_row20
    (Fin.cases first36_row21
    (Fin.cases first36_row22
    (Fin.cases first36_row23
    (Fin.cases first36_row24
    (Fin.cases first36_row25
    (Fin.cases first36_row26
    (Fin.cases first36_row27
    (Fin.cases first36_row28
    (Fin.cases first36_row29
    (Fin.cases first36_row30
    (Fin.cases first36_row31
    (Fin.cases first36_row32
    (Fin.cases first36_row33
    (Fin.cases first36_row34
    (Fin.cases first36_row35
    (Fin.cases first36_row36
    (Fin.cases first36_row37
    (Fin.cases first36_row38
    (Fin.cases first36_row39
    (Fin.cases first36_row40
    (Fin.cases first36_row41
    (Fin.cases first36_row42
    (Fin.cases first36_row43
    (Fin.cases first36_row44
    (Fin.cases first36_row45
    (Fin.cases first36_row46
    (Fin.cases first36_row47
    (Fin.cases first36_row48
    (Fin.cases first36_row49
    (Fin.cases first36_row50
    (Fin.cases first36_row51
    (Fin.cases first36_row52
    (Fin.cases first36_row53
    (Fin.cases first36_row54
    (Fin.cases first36_row55
    (Fin.cases first36_row56
    (Fin.cases first36_row57
    (Fin.cases first36_row58
    (Fin.cases first36_row59
    (Fin.cases first36_row60
    (Fin.cases first36_row61
    (Fin.cases first36_row62
    (Fin.cases first36_row63
    (Fin.cases first36_row64
    (Fin.cases first36_row65
    (Fin.cases first36_row66
    (Fin.cases first36_row67
    (Fin.cases first36_row68
    (Fin.cases first36_row69
    (Fin.cases first36_row70
    (Fin.cases first36_row71
    (Fin.cases first36_row72
    (Fin.cases first36_row73
    (Fin.cases first36_row74
    (Fin.cases first36_row75
    (Fin.cases first36_row76
    (Fin.cases first36_row77
    (Fin.cases first36_row78
    (Fin.cases first36_row79
    (Fin.cases first36_row80
    (Fin.cases first36_row81
    (Fin.cases first36_row82
    (Fin.cases first36_row83
    (Fin.cases first36_row84
    (Fin.cases first36_row85
    (Fin.cases first36_row86
    (Fin.cases first36_row87
    (Fin.cases first36_row88
    (Fin.cases first36_row89
    (Fin.cases first36_row90
    (Fin.cases first36_row91
    (Fin.cases first36_row92
    (Fin.cases first36_row93
    (Fin.cases first36_row94
    (Fin.cases first36_row95
    (Fin.cases first36_row96
    (Fin.cases first36_row97
    (Fin.cases first36_row98
    (Fin.cases first36_row99
    (Fin.cases first36_row100
    (Fin.cases first36_row101
    (Fin.cases first36_row102
    (Fin.cases first36_row103
    (Fin.cases first36_row104
    (Fin.cases first36_row105
    (Fin.cases first36_row106
    (Fin.cases first36_row107
    (Fin.cases first36_row108
    (Fin.cases first36_row109
    (Fin.cases first36_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid46 : checkValid m46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row0 :
    checkProductRow m141 m46 m142 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row1 :
    checkProductRow m141 m46 m142 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row2 :
    checkProductRow m141 m46 m142 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row3 :
    checkProductRow m141 m46 m142 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row4 :
    checkProductRow m141 m46 m142 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row5 :
    checkProductRow m141 m46 m142 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row6 :
    checkProductRow m141 m46 m142 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row7 :
    checkProductRow m141 m46 m142 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row8 :
    checkProductRow m141 m46 m142 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row9 :
    checkProductRow m141 m46 m142 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row10 :
    checkProductRow m141 m46 m142 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row11 :
    checkProductRow m141 m46 m142 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row12 :
    checkProductRow m141 m46 m142 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row13 :
    checkProductRow m141 m46 m142 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row14 :
    checkProductRow m141 m46 m142 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row15 :
    checkProductRow m141 m46 m142 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row16 :
    checkProductRow m141 m46 m142 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row17 :
    checkProductRow m141 m46 m142 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row18 :
    checkProductRow m141 m46 m142 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row19 :
    checkProductRow m141 m46 m142 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row20 :
    checkProductRow m141 m46 m142 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row21 :
    checkProductRow m141 m46 m142 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row22 :
    checkProductRow m141 m46 m142 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row23 :
    checkProductRow m141 m46 m142 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row24 :
    checkProductRow m141 m46 m142 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row25 :
    checkProductRow m141 m46 m142 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row26 :
    checkProductRow m141 m46 m142 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row27 :
    checkProductRow m141 m46 m142 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row28 :
    checkProductRow m141 m46 m142 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row29 :
    checkProductRow m141 m46 m142 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row30 :
    checkProductRow m141 m46 m142 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row31 :
    checkProductRow m141 m46 m142 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row32 :
    checkProductRow m141 m46 m142 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row33 :
    checkProductRow m141 m46 m142 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row34 :
    checkProductRow m141 m46 m142 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row35 :
    checkProductRow m141 m46 m142 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row36 :
    checkProductRow m141 m46 m142 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row37 :
    checkProductRow m141 m46 m142 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row38 :
    checkProductRow m141 m46 m142 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row39 :
    checkProductRow m141 m46 m142 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row40 :
    checkProductRow m141 m46 m142 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row41 :
    checkProductRow m141 m46 m142 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row42 :
    checkProductRow m141 m46 m142 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row43 :
    checkProductRow m141 m46 m142 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row44 :
    checkProductRow m141 m46 m142 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row45 :
    checkProductRow m141 m46 m142 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row46 :
    checkProductRow m141 m46 m142 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row47 :
    checkProductRow m141 m46 m142 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row48 :
    checkProductRow m141 m46 m142 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row49 :
    checkProductRow m141 m46 m142 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row50 :
    checkProductRow m141 m46 m142 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row51 :
    checkProductRow m141 m46 m142 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row52 :
    checkProductRow m141 m46 m142 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row53 :
    checkProductRow m141 m46 m142 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row54 :
    checkProductRow m141 m46 m142 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row55 :
    checkProductRow m141 m46 m142 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row56 :
    checkProductRow m141 m46 m142 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row57 :
    checkProductRow m141 m46 m142 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row58 :
    checkProductRow m141 m46 m142 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row59 :
    checkProductRow m141 m46 m142 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row60 :
    checkProductRow m141 m46 m142 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row61 :
    checkProductRow m141 m46 m142 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row62 :
    checkProductRow m141 m46 m142 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row63 :
    checkProductRow m141 m46 m142 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row64 :
    checkProductRow m141 m46 m142 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row65 :
    checkProductRow m141 m46 m142 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row66 :
    checkProductRow m141 m46 m142 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row67 :
    checkProductRow m141 m46 m142 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row68 :
    checkProductRow m141 m46 m142 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row69 :
    checkProductRow m141 m46 m142 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row70 :
    checkProductRow m141 m46 m142 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row71 :
    checkProductRow m141 m46 m142 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row72 :
    checkProductRow m141 m46 m142 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row73 :
    checkProductRow m141 m46 m142 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row74 :
    checkProductRow m141 m46 m142 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row75 :
    checkProductRow m141 m46 m142 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row76 :
    checkProductRow m141 m46 m142 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row77 :
    checkProductRow m141 m46 m142 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row78 :
    checkProductRow m141 m46 m142 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row79 :
    checkProductRow m141 m46 m142 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row80 :
    checkProductRow m141 m46 m142 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row81 :
    checkProductRow m141 m46 m142 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row82 :
    checkProductRow m141 m46 m142 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row83 :
    checkProductRow m141 m46 m142 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row84 :
    checkProductRow m141 m46 m142 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row85 :
    checkProductRow m141 m46 m142 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row86 :
    checkProductRow m141 m46 m142 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row87 :
    checkProductRow m141 m46 m142 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row88 :
    checkProductRow m141 m46 m142 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row89 :
    checkProductRow m141 m46 m142 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row90 :
    checkProductRow m141 m46 m142 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row91 :
    checkProductRow m141 m46 m142 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row92 :
    checkProductRow m141 m46 m142 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row93 :
    checkProductRow m141 m46 m142 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row94 :
    checkProductRow m141 m46 m142 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row95 :
    checkProductRow m141 m46 m142 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row96 :
    checkProductRow m141 m46 m142 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row97 :
    checkProductRow m141 m46 m142 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row98 :
    checkProductRow m141 m46 m142 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row99 :
    checkProductRow m141 m46 m142 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row100 :
    checkProductRow m141 m46 m142 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row101 :
    checkProductRow m141 m46 m142 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row102 :
    checkProductRow m141 m46 m142 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row103 :
    checkProductRow m141 m46 m142 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row104 :
    checkProductRow m141 m46 m142 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row105 :
    checkProductRow m141 m46 m142 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row106 :
    checkProductRow m141 m46 m142 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row107 :
    checkProductRow m141 m46 m142 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row108 :
    checkProductRow m141 m46 m142 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row109 :
    checkProductRow m141 m46 m142 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first37_row110 :
    checkProductRow m141 m46 m142 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product37 :
    decode (matrixRows 141) * decode (matrixRows 46) = decode (matrixRows 142) :=
  product_of_checked_rows m141 m46 m142 valid46
    (Fin.cases first37_row0
    (Fin.cases first37_row1
    (Fin.cases first37_row2
    (Fin.cases first37_row3
    (Fin.cases first37_row4
    (Fin.cases first37_row5
    (Fin.cases first37_row6
    (Fin.cases first37_row7
    (Fin.cases first37_row8
    (Fin.cases first37_row9
    (Fin.cases first37_row10
    (Fin.cases first37_row11
    (Fin.cases first37_row12
    (Fin.cases first37_row13
    (Fin.cases first37_row14
    (Fin.cases first37_row15
    (Fin.cases first37_row16
    (Fin.cases first37_row17
    (Fin.cases first37_row18
    (Fin.cases first37_row19
    (Fin.cases first37_row20
    (Fin.cases first37_row21
    (Fin.cases first37_row22
    (Fin.cases first37_row23
    (Fin.cases first37_row24
    (Fin.cases first37_row25
    (Fin.cases first37_row26
    (Fin.cases first37_row27
    (Fin.cases first37_row28
    (Fin.cases first37_row29
    (Fin.cases first37_row30
    (Fin.cases first37_row31
    (Fin.cases first37_row32
    (Fin.cases first37_row33
    (Fin.cases first37_row34
    (Fin.cases first37_row35
    (Fin.cases first37_row36
    (Fin.cases first37_row37
    (Fin.cases first37_row38
    (Fin.cases first37_row39
    (Fin.cases first37_row40
    (Fin.cases first37_row41
    (Fin.cases first37_row42
    (Fin.cases first37_row43
    (Fin.cases first37_row44
    (Fin.cases first37_row45
    (Fin.cases first37_row46
    (Fin.cases first37_row47
    (Fin.cases first37_row48
    (Fin.cases first37_row49
    (Fin.cases first37_row50
    (Fin.cases first37_row51
    (Fin.cases first37_row52
    (Fin.cases first37_row53
    (Fin.cases first37_row54
    (Fin.cases first37_row55
    (Fin.cases first37_row56
    (Fin.cases first37_row57
    (Fin.cases first37_row58
    (Fin.cases first37_row59
    (Fin.cases first37_row60
    (Fin.cases first37_row61
    (Fin.cases first37_row62
    (Fin.cases first37_row63
    (Fin.cases first37_row64
    (Fin.cases first37_row65
    (Fin.cases first37_row66
    (Fin.cases first37_row67
    (Fin.cases first37_row68
    (Fin.cases first37_row69
    (Fin.cases first37_row70
    (Fin.cases first37_row71
    (Fin.cases first37_row72
    (Fin.cases first37_row73
    (Fin.cases first37_row74
    (Fin.cases first37_row75
    (Fin.cases first37_row76
    (Fin.cases first37_row77
    (Fin.cases first37_row78
    (Fin.cases first37_row79
    (Fin.cases first37_row80
    (Fin.cases first37_row81
    (Fin.cases first37_row82
    (Fin.cases first37_row83
    (Fin.cases first37_row84
    (Fin.cases first37_row85
    (Fin.cases first37_row86
    (Fin.cases first37_row87
    (Fin.cases first37_row88
    (Fin.cases first37_row89
    (Fin.cases first37_row90
    (Fin.cases first37_row91
    (Fin.cases first37_row92
    (Fin.cases first37_row93
    (Fin.cases first37_row94
    (Fin.cases first37_row95
    (Fin.cases first37_row96
    (Fin.cases first37_row97
    (Fin.cases first37_row98
    (Fin.cases first37_row99
    (Fin.cases first37_row100
    (Fin.cases first37_row101
    (Fin.cases first37_row102
    (Fin.cases first37_row103
    (Fin.cases first37_row104
    (Fin.cases first37_row105
    (Fin.cases first37_row106
    (Fin.cases first37_row107
    (Fin.cases first37_row108
    (Fin.cases first37_row109
    (Fin.cases first37_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid9 : checkValid m9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row0 :
    checkProductRow m142 m9 m143 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row1 :
    checkProductRow m142 m9 m143 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row2 :
    checkProductRow m142 m9 m143 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row3 :
    checkProductRow m142 m9 m143 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row4 :
    checkProductRow m142 m9 m143 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row5 :
    checkProductRow m142 m9 m143 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row6 :
    checkProductRow m142 m9 m143 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row7 :
    checkProductRow m142 m9 m143 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row8 :
    checkProductRow m142 m9 m143 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row9 :
    checkProductRow m142 m9 m143 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row10 :
    checkProductRow m142 m9 m143 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row11 :
    checkProductRow m142 m9 m143 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row12 :
    checkProductRow m142 m9 m143 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row13 :
    checkProductRow m142 m9 m143 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row14 :
    checkProductRow m142 m9 m143 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row15 :
    checkProductRow m142 m9 m143 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row16 :
    checkProductRow m142 m9 m143 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row17 :
    checkProductRow m142 m9 m143 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row18 :
    checkProductRow m142 m9 m143 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row19 :
    checkProductRow m142 m9 m143 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row20 :
    checkProductRow m142 m9 m143 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row21 :
    checkProductRow m142 m9 m143 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row22 :
    checkProductRow m142 m9 m143 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row23 :
    checkProductRow m142 m9 m143 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row24 :
    checkProductRow m142 m9 m143 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row25 :
    checkProductRow m142 m9 m143 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row26 :
    checkProductRow m142 m9 m143 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row27 :
    checkProductRow m142 m9 m143 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row28 :
    checkProductRow m142 m9 m143 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row29 :
    checkProductRow m142 m9 m143 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row30 :
    checkProductRow m142 m9 m143 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row31 :
    checkProductRow m142 m9 m143 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row32 :
    checkProductRow m142 m9 m143 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row33 :
    checkProductRow m142 m9 m143 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row34 :
    checkProductRow m142 m9 m143 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row35 :
    checkProductRow m142 m9 m143 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row36 :
    checkProductRow m142 m9 m143 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row37 :
    checkProductRow m142 m9 m143 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row38 :
    checkProductRow m142 m9 m143 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row39 :
    checkProductRow m142 m9 m143 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row40 :
    checkProductRow m142 m9 m143 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row41 :
    checkProductRow m142 m9 m143 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row42 :
    checkProductRow m142 m9 m143 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row43 :
    checkProductRow m142 m9 m143 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row44 :
    checkProductRow m142 m9 m143 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row45 :
    checkProductRow m142 m9 m143 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row46 :
    checkProductRow m142 m9 m143 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row47 :
    checkProductRow m142 m9 m143 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row48 :
    checkProductRow m142 m9 m143 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row49 :
    checkProductRow m142 m9 m143 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row50 :
    checkProductRow m142 m9 m143 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row51 :
    checkProductRow m142 m9 m143 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row52 :
    checkProductRow m142 m9 m143 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row53 :
    checkProductRow m142 m9 m143 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row54 :
    checkProductRow m142 m9 m143 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row55 :
    checkProductRow m142 m9 m143 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row56 :
    checkProductRow m142 m9 m143 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row57 :
    checkProductRow m142 m9 m143 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row58 :
    checkProductRow m142 m9 m143 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row59 :
    checkProductRow m142 m9 m143 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row60 :
    checkProductRow m142 m9 m143 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row61 :
    checkProductRow m142 m9 m143 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row62 :
    checkProductRow m142 m9 m143 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row63 :
    checkProductRow m142 m9 m143 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row64 :
    checkProductRow m142 m9 m143 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row65 :
    checkProductRow m142 m9 m143 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row66 :
    checkProductRow m142 m9 m143 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row67 :
    checkProductRow m142 m9 m143 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row68 :
    checkProductRow m142 m9 m143 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row69 :
    checkProductRow m142 m9 m143 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row70 :
    checkProductRow m142 m9 m143 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row71 :
    checkProductRow m142 m9 m143 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row72 :
    checkProductRow m142 m9 m143 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row73 :
    checkProductRow m142 m9 m143 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row74 :
    checkProductRow m142 m9 m143 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row75 :
    checkProductRow m142 m9 m143 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row76 :
    checkProductRow m142 m9 m143 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row77 :
    checkProductRow m142 m9 m143 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row78 :
    checkProductRow m142 m9 m143 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row79 :
    checkProductRow m142 m9 m143 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row80 :
    checkProductRow m142 m9 m143 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row81 :
    checkProductRow m142 m9 m143 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row82 :
    checkProductRow m142 m9 m143 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row83 :
    checkProductRow m142 m9 m143 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row84 :
    checkProductRow m142 m9 m143 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row85 :
    checkProductRow m142 m9 m143 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row86 :
    checkProductRow m142 m9 m143 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row87 :
    checkProductRow m142 m9 m143 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row88 :
    checkProductRow m142 m9 m143 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row89 :
    checkProductRow m142 m9 m143 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row90 :
    checkProductRow m142 m9 m143 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row91 :
    checkProductRow m142 m9 m143 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row92 :
    checkProductRow m142 m9 m143 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row93 :
    checkProductRow m142 m9 m143 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row94 :
    checkProductRow m142 m9 m143 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row95 :
    checkProductRow m142 m9 m143 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row96 :
    checkProductRow m142 m9 m143 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row97 :
    checkProductRow m142 m9 m143 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row98 :
    checkProductRow m142 m9 m143 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row99 :
    checkProductRow m142 m9 m143 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row100 :
    checkProductRow m142 m9 m143 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row101 :
    checkProductRow m142 m9 m143 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row102 :
    checkProductRow m142 m9 m143 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row103 :
    checkProductRow m142 m9 m143 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row104 :
    checkProductRow m142 m9 m143 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row105 :
    checkProductRow m142 m9 m143 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row106 :
    checkProductRow m142 m9 m143 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row107 :
    checkProductRow m142 m9 m143 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row108 :
    checkProductRow m142 m9 m143 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row109 :
    checkProductRow m142 m9 m143 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first38_row110 :
    checkProductRow m142 m9 m143 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product38 :
    decode (matrixRows 142) * decode (matrixRows 9) = decode (matrixRows 143) :=
  product_of_checked_rows m142 m9 m143 valid9
    (Fin.cases first38_row0
    (Fin.cases first38_row1
    (Fin.cases first38_row2
    (Fin.cases first38_row3
    (Fin.cases first38_row4
    (Fin.cases first38_row5
    (Fin.cases first38_row6
    (Fin.cases first38_row7
    (Fin.cases first38_row8
    (Fin.cases first38_row9
    (Fin.cases first38_row10
    (Fin.cases first38_row11
    (Fin.cases first38_row12
    (Fin.cases first38_row13
    (Fin.cases first38_row14
    (Fin.cases first38_row15
    (Fin.cases first38_row16
    (Fin.cases first38_row17
    (Fin.cases first38_row18
    (Fin.cases first38_row19
    (Fin.cases first38_row20
    (Fin.cases first38_row21
    (Fin.cases first38_row22
    (Fin.cases first38_row23
    (Fin.cases first38_row24
    (Fin.cases first38_row25
    (Fin.cases first38_row26
    (Fin.cases first38_row27
    (Fin.cases first38_row28
    (Fin.cases first38_row29
    (Fin.cases first38_row30
    (Fin.cases first38_row31
    (Fin.cases first38_row32
    (Fin.cases first38_row33
    (Fin.cases first38_row34
    (Fin.cases first38_row35
    (Fin.cases first38_row36
    (Fin.cases first38_row37
    (Fin.cases first38_row38
    (Fin.cases first38_row39
    (Fin.cases first38_row40
    (Fin.cases first38_row41
    (Fin.cases first38_row42
    (Fin.cases first38_row43
    (Fin.cases first38_row44
    (Fin.cases first38_row45
    (Fin.cases first38_row46
    (Fin.cases first38_row47
    (Fin.cases first38_row48
    (Fin.cases first38_row49
    (Fin.cases first38_row50
    (Fin.cases first38_row51
    (Fin.cases first38_row52
    (Fin.cases first38_row53
    (Fin.cases first38_row54
    (Fin.cases first38_row55
    (Fin.cases first38_row56
    (Fin.cases first38_row57
    (Fin.cases first38_row58
    (Fin.cases first38_row59
    (Fin.cases first38_row60
    (Fin.cases first38_row61
    (Fin.cases first38_row62
    (Fin.cases first38_row63
    (Fin.cases first38_row64
    (Fin.cases first38_row65
    (Fin.cases first38_row66
    (Fin.cases first38_row67
    (Fin.cases first38_row68
    (Fin.cases first38_row69
    (Fin.cases first38_row70
    (Fin.cases first38_row71
    (Fin.cases first38_row72
    (Fin.cases first38_row73
    (Fin.cases first38_row74
    (Fin.cases first38_row75
    (Fin.cases first38_row76
    (Fin.cases first38_row77
    (Fin.cases first38_row78
    (Fin.cases first38_row79
    (Fin.cases first38_row80
    (Fin.cases first38_row81
    (Fin.cases first38_row82
    (Fin.cases first38_row83
    (Fin.cases first38_row84
    (Fin.cases first38_row85
    (Fin.cases first38_row86
    (Fin.cases first38_row87
    (Fin.cases first38_row88
    (Fin.cases first38_row89
    (Fin.cases first38_row90
    (Fin.cases first38_row91
    (Fin.cases first38_row92
    (Fin.cases first38_row93
    (Fin.cases first38_row94
    (Fin.cases first38_row95
    (Fin.cases first38_row96
    (Fin.cases first38_row97
    (Fin.cases first38_row98
    (Fin.cases first38_row99
    (Fin.cases first38_row100
    (Fin.cases first38_row101
    (Fin.cases first38_row102
    (Fin.cases first38_row103
    (Fin.cases first38_row104
    (Fin.cases first38_row105
    (Fin.cases first38_row106
    (Fin.cases first38_row107
    (Fin.cases first38_row108
    (Fin.cases first38_row109
    (Fin.cases first38_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid59 : checkValid m59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row0 :
    checkProductRow m143 m59 m144 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row1 :
    checkProductRow m143 m59 m144 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row2 :
    checkProductRow m143 m59 m144 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row3 :
    checkProductRow m143 m59 m144 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row4 :
    checkProductRow m143 m59 m144 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row5 :
    checkProductRow m143 m59 m144 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row6 :
    checkProductRow m143 m59 m144 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row7 :
    checkProductRow m143 m59 m144 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row8 :
    checkProductRow m143 m59 m144 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row9 :
    checkProductRow m143 m59 m144 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row10 :
    checkProductRow m143 m59 m144 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row11 :
    checkProductRow m143 m59 m144 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row12 :
    checkProductRow m143 m59 m144 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row13 :
    checkProductRow m143 m59 m144 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row14 :
    checkProductRow m143 m59 m144 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row15 :
    checkProductRow m143 m59 m144 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row16 :
    checkProductRow m143 m59 m144 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row17 :
    checkProductRow m143 m59 m144 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row18 :
    checkProductRow m143 m59 m144 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row19 :
    checkProductRow m143 m59 m144 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row20 :
    checkProductRow m143 m59 m144 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row21 :
    checkProductRow m143 m59 m144 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row22 :
    checkProductRow m143 m59 m144 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row23 :
    checkProductRow m143 m59 m144 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row24 :
    checkProductRow m143 m59 m144 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row25 :
    checkProductRow m143 m59 m144 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row26 :
    checkProductRow m143 m59 m144 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row27 :
    checkProductRow m143 m59 m144 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row28 :
    checkProductRow m143 m59 m144 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row29 :
    checkProductRow m143 m59 m144 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row30 :
    checkProductRow m143 m59 m144 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row31 :
    checkProductRow m143 m59 m144 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row32 :
    checkProductRow m143 m59 m144 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row33 :
    checkProductRow m143 m59 m144 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row34 :
    checkProductRow m143 m59 m144 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row35 :
    checkProductRow m143 m59 m144 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row36 :
    checkProductRow m143 m59 m144 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row37 :
    checkProductRow m143 m59 m144 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row38 :
    checkProductRow m143 m59 m144 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row39 :
    checkProductRow m143 m59 m144 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row40 :
    checkProductRow m143 m59 m144 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row41 :
    checkProductRow m143 m59 m144 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row42 :
    checkProductRow m143 m59 m144 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row43 :
    checkProductRow m143 m59 m144 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row44 :
    checkProductRow m143 m59 m144 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row45 :
    checkProductRow m143 m59 m144 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row46 :
    checkProductRow m143 m59 m144 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row47 :
    checkProductRow m143 m59 m144 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row48 :
    checkProductRow m143 m59 m144 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row49 :
    checkProductRow m143 m59 m144 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row50 :
    checkProductRow m143 m59 m144 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row51 :
    checkProductRow m143 m59 m144 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row52 :
    checkProductRow m143 m59 m144 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row53 :
    checkProductRow m143 m59 m144 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row54 :
    checkProductRow m143 m59 m144 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row55 :
    checkProductRow m143 m59 m144 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row56 :
    checkProductRow m143 m59 m144 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row57 :
    checkProductRow m143 m59 m144 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row58 :
    checkProductRow m143 m59 m144 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row59 :
    checkProductRow m143 m59 m144 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row60 :
    checkProductRow m143 m59 m144 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row61 :
    checkProductRow m143 m59 m144 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row62 :
    checkProductRow m143 m59 m144 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row63 :
    checkProductRow m143 m59 m144 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row64 :
    checkProductRow m143 m59 m144 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row65 :
    checkProductRow m143 m59 m144 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row66 :
    checkProductRow m143 m59 m144 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row67 :
    checkProductRow m143 m59 m144 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row68 :
    checkProductRow m143 m59 m144 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row69 :
    checkProductRow m143 m59 m144 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row70 :
    checkProductRow m143 m59 m144 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row71 :
    checkProductRow m143 m59 m144 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row72 :
    checkProductRow m143 m59 m144 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row73 :
    checkProductRow m143 m59 m144 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row74 :
    checkProductRow m143 m59 m144 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row75 :
    checkProductRow m143 m59 m144 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row76 :
    checkProductRow m143 m59 m144 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row77 :
    checkProductRow m143 m59 m144 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row78 :
    checkProductRow m143 m59 m144 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row79 :
    checkProductRow m143 m59 m144 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row80 :
    checkProductRow m143 m59 m144 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row81 :
    checkProductRow m143 m59 m144 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row82 :
    checkProductRow m143 m59 m144 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row83 :
    checkProductRow m143 m59 m144 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row84 :
    checkProductRow m143 m59 m144 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row85 :
    checkProductRow m143 m59 m144 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row86 :
    checkProductRow m143 m59 m144 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row87 :
    checkProductRow m143 m59 m144 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row88 :
    checkProductRow m143 m59 m144 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row89 :
    checkProductRow m143 m59 m144 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row90 :
    checkProductRow m143 m59 m144 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row91 :
    checkProductRow m143 m59 m144 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row92 :
    checkProductRow m143 m59 m144 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row93 :
    checkProductRow m143 m59 m144 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row94 :
    checkProductRow m143 m59 m144 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row95 :
    checkProductRow m143 m59 m144 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row96 :
    checkProductRow m143 m59 m144 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row97 :
    checkProductRow m143 m59 m144 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row98 :
    checkProductRow m143 m59 m144 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row99 :
    checkProductRow m143 m59 m144 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row100 :
    checkProductRow m143 m59 m144 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row101 :
    checkProductRow m143 m59 m144 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row102 :
    checkProductRow m143 m59 m144 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row103 :
    checkProductRow m143 m59 m144 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row104 :
    checkProductRow m143 m59 m144 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row105 :
    checkProductRow m143 m59 m144 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row106 :
    checkProductRow m143 m59 m144 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row107 :
    checkProductRow m143 m59 m144 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row108 :
    checkProductRow m143 m59 m144 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row109 :
    checkProductRow m143 m59 m144 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first39_row110 :
    checkProductRow m143 m59 m144 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product39 :
    decode (matrixRows 143) * decode (matrixRows 59) = decode (matrixRows 144) :=
  product_of_checked_rows m143 m59 m144 valid59
    (Fin.cases first39_row0
    (Fin.cases first39_row1
    (Fin.cases first39_row2
    (Fin.cases first39_row3
    (Fin.cases first39_row4
    (Fin.cases first39_row5
    (Fin.cases first39_row6
    (Fin.cases first39_row7
    (Fin.cases first39_row8
    (Fin.cases first39_row9
    (Fin.cases first39_row10
    (Fin.cases first39_row11
    (Fin.cases first39_row12
    (Fin.cases first39_row13
    (Fin.cases first39_row14
    (Fin.cases first39_row15
    (Fin.cases first39_row16
    (Fin.cases first39_row17
    (Fin.cases first39_row18
    (Fin.cases first39_row19
    (Fin.cases first39_row20
    (Fin.cases first39_row21
    (Fin.cases first39_row22
    (Fin.cases first39_row23
    (Fin.cases first39_row24
    (Fin.cases first39_row25
    (Fin.cases first39_row26
    (Fin.cases first39_row27
    (Fin.cases first39_row28
    (Fin.cases first39_row29
    (Fin.cases first39_row30
    (Fin.cases first39_row31
    (Fin.cases first39_row32
    (Fin.cases first39_row33
    (Fin.cases first39_row34
    (Fin.cases first39_row35
    (Fin.cases first39_row36
    (Fin.cases first39_row37
    (Fin.cases first39_row38
    (Fin.cases first39_row39
    (Fin.cases first39_row40
    (Fin.cases first39_row41
    (Fin.cases first39_row42
    (Fin.cases first39_row43
    (Fin.cases first39_row44
    (Fin.cases first39_row45
    (Fin.cases first39_row46
    (Fin.cases first39_row47
    (Fin.cases first39_row48
    (Fin.cases first39_row49
    (Fin.cases first39_row50
    (Fin.cases first39_row51
    (Fin.cases first39_row52
    (Fin.cases first39_row53
    (Fin.cases first39_row54
    (Fin.cases first39_row55
    (Fin.cases first39_row56
    (Fin.cases first39_row57
    (Fin.cases first39_row58
    (Fin.cases first39_row59
    (Fin.cases first39_row60
    (Fin.cases first39_row61
    (Fin.cases first39_row62
    (Fin.cases first39_row63
    (Fin.cases first39_row64
    (Fin.cases first39_row65
    (Fin.cases first39_row66
    (Fin.cases first39_row67
    (Fin.cases first39_row68
    (Fin.cases first39_row69
    (Fin.cases first39_row70
    (Fin.cases first39_row71
    (Fin.cases first39_row72
    (Fin.cases first39_row73
    (Fin.cases first39_row74
    (Fin.cases first39_row75
    (Fin.cases first39_row76
    (Fin.cases first39_row77
    (Fin.cases first39_row78
    (Fin.cases first39_row79
    (Fin.cases first39_row80
    (Fin.cases first39_row81
    (Fin.cases first39_row82
    (Fin.cases first39_row83
    (Fin.cases first39_row84
    (Fin.cases first39_row85
    (Fin.cases first39_row86
    (Fin.cases first39_row87
    (Fin.cases first39_row88
    (Fin.cases first39_row89
    (Fin.cases first39_row90
    (Fin.cases first39_row91
    (Fin.cases first39_row92
    (Fin.cases first39_row93
    (Fin.cases first39_row94
    (Fin.cases first39_row95
    (Fin.cases first39_row96
    (Fin.cases first39_row97
    (Fin.cases first39_row98
    (Fin.cases first39_row99
    (Fin.cases first39_row100
    (Fin.cases first39_row101
    (Fin.cases first39_row102
    (Fin.cases first39_row103
    (Fin.cases first39_row104
    (Fin.cases first39_row105
    (Fin.cases first39_row106
    (Fin.cases first39_row107
    (Fin.cases first39_row108
    (Fin.cases first39_row109
    (Fin.cases first39_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid24 : checkValid m24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row0 :
    checkProductRow m144 m24 m145 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row1 :
    checkProductRow m144 m24 m145 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row2 :
    checkProductRow m144 m24 m145 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row3 :
    checkProductRow m144 m24 m145 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row4 :
    checkProductRow m144 m24 m145 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row5 :
    checkProductRow m144 m24 m145 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row6 :
    checkProductRow m144 m24 m145 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row7 :
    checkProductRow m144 m24 m145 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row8 :
    checkProductRow m144 m24 m145 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row9 :
    checkProductRow m144 m24 m145 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row10 :
    checkProductRow m144 m24 m145 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row11 :
    checkProductRow m144 m24 m145 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row12 :
    checkProductRow m144 m24 m145 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row13 :
    checkProductRow m144 m24 m145 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row14 :
    checkProductRow m144 m24 m145 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row15 :
    checkProductRow m144 m24 m145 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row16 :
    checkProductRow m144 m24 m145 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row17 :
    checkProductRow m144 m24 m145 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row18 :
    checkProductRow m144 m24 m145 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row19 :
    checkProductRow m144 m24 m145 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row20 :
    checkProductRow m144 m24 m145 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row21 :
    checkProductRow m144 m24 m145 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row22 :
    checkProductRow m144 m24 m145 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row23 :
    checkProductRow m144 m24 m145 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row24 :
    checkProductRow m144 m24 m145 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row25 :
    checkProductRow m144 m24 m145 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row26 :
    checkProductRow m144 m24 m145 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row27 :
    checkProductRow m144 m24 m145 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row28 :
    checkProductRow m144 m24 m145 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row29 :
    checkProductRow m144 m24 m145 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row30 :
    checkProductRow m144 m24 m145 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row31 :
    checkProductRow m144 m24 m145 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row32 :
    checkProductRow m144 m24 m145 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row33 :
    checkProductRow m144 m24 m145 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row34 :
    checkProductRow m144 m24 m145 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row35 :
    checkProductRow m144 m24 m145 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row36 :
    checkProductRow m144 m24 m145 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row37 :
    checkProductRow m144 m24 m145 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row38 :
    checkProductRow m144 m24 m145 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row39 :
    checkProductRow m144 m24 m145 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row40 :
    checkProductRow m144 m24 m145 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row41 :
    checkProductRow m144 m24 m145 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row42 :
    checkProductRow m144 m24 m145 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row43 :
    checkProductRow m144 m24 m145 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row44 :
    checkProductRow m144 m24 m145 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row45 :
    checkProductRow m144 m24 m145 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row46 :
    checkProductRow m144 m24 m145 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row47 :
    checkProductRow m144 m24 m145 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row48 :
    checkProductRow m144 m24 m145 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row49 :
    checkProductRow m144 m24 m145 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row50 :
    checkProductRow m144 m24 m145 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row51 :
    checkProductRow m144 m24 m145 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row52 :
    checkProductRow m144 m24 m145 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row53 :
    checkProductRow m144 m24 m145 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row54 :
    checkProductRow m144 m24 m145 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row55 :
    checkProductRow m144 m24 m145 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row56 :
    checkProductRow m144 m24 m145 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row57 :
    checkProductRow m144 m24 m145 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row58 :
    checkProductRow m144 m24 m145 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row59 :
    checkProductRow m144 m24 m145 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row60 :
    checkProductRow m144 m24 m145 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row61 :
    checkProductRow m144 m24 m145 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row62 :
    checkProductRow m144 m24 m145 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row63 :
    checkProductRow m144 m24 m145 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row64 :
    checkProductRow m144 m24 m145 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row65 :
    checkProductRow m144 m24 m145 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row66 :
    checkProductRow m144 m24 m145 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row67 :
    checkProductRow m144 m24 m145 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row68 :
    checkProductRow m144 m24 m145 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row69 :
    checkProductRow m144 m24 m145 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row70 :
    checkProductRow m144 m24 m145 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row71 :
    checkProductRow m144 m24 m145 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row72 :
    checkProductRow m144 m24 m145 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row73 :
    checkProductRow m144 m24 m145 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row74 :
    checkProductRow m144 m24 m145 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row75 :
    checkProductRow m144 m24 m145 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row76 :
    checkProductRow m144 m24 m145 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row77 :
    checkProductRow m144 m24 m145 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row78 :
    checkProductRow m144 m24 m145 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row79 :
    checkProductRow m144 m24 m145 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row80 :
    checkProductRow m144 m24 m145 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row81 :
    checkProductRow m144 m24 m145 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row82 :
    checkProductRow m144 m24 m145 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row83 :
    checkProductRow m144 m24 m145 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row84 :
    checkProductRow m144 m24 m145 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row85 :
    checkProductRow m144 m24 m145 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row86 :
    checkProductRow m144 m24 m145 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row87 :
    checkProductRow m144 m24 m145 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row88 :
    checkProductRow m144 m24 m145 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row89 :
    checkProductRow m144 m24 m145 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row90 :
    checkProductRow m144 m24 m145 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row91 :
    checkProductRow m144 m24 m145 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row92 :
    checkProductRow m144 m24 m145 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row93 :
    checkProductRow m144 m24 m145 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row94 :
    checkProductRow m144 m24 m145 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row95 :
    checkProductRow m144 m24 m145 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row96 :
    checkProductRow m144 m24 m145 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row97 :
    checkProductRow m144 m24 m145 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row98 :
    checkProductRow m144 m24 m145 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row99 :
    checkProductRow m144 m24 m145 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row100 :
    checkProductRow m144 m24 m145 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row101 :
    checkProductRow m144 m24 m145 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row102 :
    checkProductRow m144 m24 m145 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row103 :
    checkProductRow m144 m24 m145 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row104 :
    checkProductRow m144 m24 m145 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row105 :
    checkProductRow m144 m24 m145 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row106 :
    checkProductRow m144 m24 m145 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row107 :
    checkProductRow m144 m24 m145 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row108 :
    checkProductRow m144 m24 m145 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row109 :
    checkProductRow m144 m24 m145 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem first40_row110 :
    checkProductRow m144 m24 m145 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem first_product40 :
    decode (matrixRows 144) * decode (matrixRows 24) = decode (matrixRows 145) :=
  product_of_checked_rows m144 m24 m145 valid24
    (Fin.cases first40_row0
    (Fin.cases first40_row1
    (Fin.cases first40_row2
    (Fin.cases first40_row3
    (Fin.cases first40_row4
    (Fin.cases first40_row5
    (Fin.cases first40_row6
    (Fin.cases first40_row7
    (Fin.cases first40_row8
    (Fin.cases first40_row9
    (Fin.cases first40_row10
    (Fin.cases first40_row11
    (Fin.cases first40_row12
    (Fin.cases first40_row13
    (Fin.cases first40_row14
    (Fin.cases first40_row15
    (Fin.cases first40_row16
    (Fin.cases first40_row17
    (Fin.cases first40_row18
    (Fin.cases first40_row19
    (Fin.cases first40_row20
    (Fin.cases first40_row21
    (Fin.cases first40_row22
    (Fin.cases first40_row23
    (Fin.cases first40_row24
    (Fin.cases first40_row25
    (Fin.cases first40_row26
    (Fin.cases first40_row27
    (Fin.cases first40_row28
    (Fin.cases first40_row29
    (Fin.cases first40_row30
    (Fin.cases first40_row31
    (Fin.cases first40_row32
    (Fin.cases first40_row33
    (Fin.cases first40_row34
    (Fin.cases first40_row35
    (Fin.cases first40_row36
    (Fin.cases first40_row37
    (Fin.cases first40_row38
    (Fin.cases first40_row39
    (Fin.cases first40_row40
    (Fin.cases first40_row41
    (Fin.cases first40_row42
    (Fin.cases first40_row43
    (Fin.cases first40_row44
    (Fin.cases first40_row45
    (Fin.cases first40_row46
    (Fin.cases first40_row47
    (Fin.cases first40_row48
    (Fin.cases first40_row49
    (Fin.cases first40_row50
    (Fin.cases first40_row51
    (Fin.cases first40_row52
    (Fin.cases first40_row53
    (Fin.cases first40_row54
    (Fin.cases first40_row55
    (Fin.cases first40_row56
    (Fin.cases first40_row57
    (Fin.cases first40_row58
    (Fin.cases first40_row59
    (Fin.cases first40_row60
    (Fin.cases first40_row61
    (Fin.cases first40_row62
    (Fin.cases first40_row63
    (Fin.cases first40_row64
    (Fin.cases first40_row65
    (Fin.cases first40_row66
    (Fin.cases first40_row67
    (Fin.cases first40_row68
    (Fin.cases first40_row69
    (Fin.cases first40_row70
    (Fin.cases first40_row71
    (Fin.cases first40_row72
    (Fin.cases first40_row73
    (Fin.cases first40_row74
    (Fin.cases first40_row75
    (Fin.cases first40_row76
    (Fin.cases first40_row77
    (Fin.cases first40_row78
    (Fin.cases first40_row79
    (Fin.cases first40_row80
    (Fin.cases first40_row81
    (Fin.cases first40_row82
    (Fin.cases first40_row83
    (Fin.cases first40_row84
    (Fin.cases first40_row85
    (Fin.cases first40_row86
    (Fin.cases first40_row87
    (Fin.cases first40_row88
    (Fin.cases first40_row89
    (Fin.cases first40_row90
    (Fin.cases first40_row91
    (Fin.cases first40_row92
    (Fin.cases first40_row93
    (Fin.cases first40_row94
    (Fin.cases first40_row95
    (Fin.cases first40_row96
    (Fin.cases first40_row97
    (Fin.cases first40_row98
    (Fin.cases first40_row99
    (Fin.cases first40_row100
    (Fin.cases first40_row101
    (Fin.cases first40_row102
    (Fin.cases first40_row103
    (Fin.cases first40_row104
    (Fin.cases first40_row105
    (Fin.cases first40_row106
    (Fin.cases first40_row107
    (Fin.cases first40_row108
    (Fin.cases first40_row109
    (Fin.cases first40_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.RelationCertificate
