module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts

/-!
# Shared-subword products 64–67 for the local presentation

Each row equality is checked by kernel reduction. The proved packed-row
soundness theorem converts the checks to ordinary matrix multiplication.
Source data and reproducible generation: `Atlas111LocalRelationSource/`.
-/

namespace Lyons.RelationCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid20 : checkValid m20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row0 :
    checkProductRow m67 m20 m68 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row1 :
    checkProductRow m67 m20 m68 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row2 :
    checkProductRow m67 m20 m68 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row3 :
    checkProductRow m67 m20 m68 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row4 :
    checkProductRow m67 m20 m68 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row5 :
    checkProductRow m67 m20 m68 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row6 :
    checkProductRow m67 m20 m68 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row7 :
    checkProductRow m67 m20 m68 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row8 :
    checkProductRow m67 m20 m68 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row9 :
    checkProductRow m67 m20 m68 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row10 :
    checkProductRow m67 m20 m68 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row11 :
    checkProductRow m67 m20 m68 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row12 :
    checkProductRow m67 m20 m68 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row13 :
    checkProductRow m67 m20 m68 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row14 :
    checkProductRow m67 m20 m68 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row15 :
    checkProductRow m67 m20 m68 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row16 :
    checkProductRow m67 m20 m68 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row17 :
    checkProductRow m67 m20 m68 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row18 :
    checkProductRow m67 m20 m68 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row19 :
    checkProductRow m67 m20 m68 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row20 :
    checkProductRow m67 m20 m68 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row21 :
    checkProductRow m67 m20 m68 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row22 :
    checkProductRow m67 m20 m68 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row23 :
    checkProductRow m67 m20 m68 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row24 :
    checkProductRow m67 m20 m68 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row25 :
    checkProductRow m67 m20 m68 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row26 :
    checkProductRow m67 m20 m68 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row27 :
    checkProductRow m67 m20 m68 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row28 :
    checkProductRow m67 m20 m68 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row29 :
    checkProductRow m67 m20 m68 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row30 :
    checkProductRow m67 m20 m68 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row31 :
    checkProductRow m67 m20 m68 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row32 :
    checkProductRow m67 m20 m68 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row33 :
    checkProductRow m67 m20 m68 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row34 :
    checkProductRow m67 m20 m68 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row35 :
    checkProductRow m67 m20 m68 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row36 :
    checkProductRow m67 m20 m68 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row37 :
    checkProductRow m67 m20 m68 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row38 :
    checkProductRow m67 m20 m68 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row39 :
    checkProductRow m67 m20 m68 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row40 :
    checkProductRow m67 m20 m68 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row41 :
    checkProductRow m67 m20 m68 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row42 :
    checkProductRow m67 m20 m68 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row43 :
    checkProductRow m67 m20 m68 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row44 :
    checkProductRow m67 m20 m68 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row45 :
    checkProductRow m67 m20 m68 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row46 :
    checkProductRow m67 m20 m68 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row47 :
    checkProductRow m67 m20 m68 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row48 :
    checkProductRow m67 m20 m68 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row49 :
    checkProductRow m67 m20 m68 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row50 :
    checkProductRow m67 m20 m68 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row51 :
    checkProductRow m67 m20 m68 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row52 :
    checkProductRow m67 m20 m68 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row53 :
    checkProductRow m67 m20 m68 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row54 :
    checkProductRow m67 m20 m68 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row55 :
    checkProductRow m67 m20 m68 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row56 :
    checkProductRow m67 m20 m68 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row57 :
    checkProductRow m67 m20 m68 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row58 :
    checkProductRow m67 m20 m68 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row59 :
    checkProductRow m67 m20 m68 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row60 :
    checkProductRow m67 m20 m68 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row61 :
    checkProductRow m67 m20 m68 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row62 :
    checkProductRow m67 m20 m68 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row63 :
    checkProductRow m67 m20 m68 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row64 :
    checkProductRow m67 m20 m68 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row65 :
    checkProductRow m67 m20 m68 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row66 :
    checkProductRow m67 m20 m68 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row67 :
    checkProductRow m67 m20 m68 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row68 :
    checkProductRow m67 m20 m68 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row69 :
    checkProductRow m67 m20 m68 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row70 :
    checkProductRow m67 m20 m68 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row71 :
    checkProductRow m67 m20 m68 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row72 :
    checkProductRow m67 m20 m68 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row73 :
    checkProductRow m67 m20 m68 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row74 :
    checkProductRow m67 m20 m68 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row75 :
    checkProductRow m67 m20 m68 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row76 :
    checkProductRow m67 m20 m68 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row77 :
    checkProductRow m67 m20 m68 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row78 :
    checkProductRow m67 m20 m68 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row79 :
    checkProductRow m67 m20 m68 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row80 :
    checkProductRow m67 m20 m68 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row81 :
    checkProductRow m67 m20 m68 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row82 :
    checkProductRow m67 m20 m68 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row83 :
    checkProductRow m67 m20 m68 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row84 :
    checkProductRow m67 m20 m68 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row85 :
    checkProductRow m67 m20 m68 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row86 :
    checkProductRow m67 m20 m68 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row87 :
    checkProductRow m67 m20 m68 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row88 :
    checkProductRow m67 m20 m68 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row89 :
    checkProductRow m67 m20 m68 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row90 :
    checkProductRow m67 m20 m68 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row91 :
    checkProductRow m67 m20 m68 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row92 :
    checkProductRow m67 m20 m68 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row93 :
    checkProductRow m67 m20 m68 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row94 :
    checkProductRow m67 m20 m68 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row95 :
    checkProductRow m67 m20 m68 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row96 :
    checkProductRow m67 m20 m68 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row97 :
    checkProductRow m67 m20 m68 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row98 :
    checkProductRow m67 m20 m68 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row99 :
    checkProductRow m67 m20 m68 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row100 :
    checkProductRow m67 m20 m68 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row101 :
    checkProductRow m67 m20 m68 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row102 :
    checkProductRow m67 m20 m68 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row103 :
    checkProductRow m67 m20 m68 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row104 :
    checkProductRow m67 m20 m68 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row105 :
    checkProductRow m67 m20 m68 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row106 :
    checkProductRow m67 m20 m68 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row107 :
    checkProductRow m67 m20 m68 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row108 :
    checkProductRow m67 m20 m68 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row109 :
    checkProductRow m67 m20 m68 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared64_row110 :
    checkProductRow m67 m20 m68 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem shared_product64 :
    decode (matrixRows 67) * decode (matrixRows 20) = decode (matrixRows 68) :=
  product_of_checked_rows m67 m20 m68 valid20
    (Fin.cases shared64_row0
    (Fin.cases shared64_row1
    (Fin.cases shared64_row2
    (Fin.cases shared64_row3
    (Fin.cases shared64_row4
    (Fin.cases shared64_row5
    (Fin.cases shared64_row6
    (Fin.cases shared64_row7
    (Fin.cases shared64_row8
    (Fin.cases shared64_row9
    (Fin.cases shared64_row10
    (Fin.cases shared64_row11
    (Fin.cases shared64_row12
    (Fin.cases shared64_row13
    (Fin.cases shared64_row14
    (Fin.cases shared64_row15
    (Fin.cases shared64_row16
    (Fin.cases shared64_row17
    (Fin.cases shared64_row18
    (Fin.cases shared64_row19
    (Fin.cases shared64_row20
    (Fin.cases shared64_row21
    (Fin.cases shared64_row22
    (Fin.cases shared64_row23
    (Fin.cases shared64_row24
    (Fin.cases shared64_row25
    (Fin.cases shared64_row26
    (Fin.cases shared64_row27
    (Fin.cases shared64_row28
    (Fin.cases shared64_row29
    (Fin.cases shared64_row30
    (Fin.cases shared64_row31
    (Fin.cases shared64_row32
    (Fin.cases shared64_row33
    (Fin.cases shared64_row34
    (Fin.cases shared64_row35
    (Fin.cases shared64_row36
    (Fin.cases shared64_row37
    (Fin.cases shared64_row38
    (Fin.cases shared64_row39
    (Fin.cases shared64_row40
    (Fin.cases shared64_row41
    (Fin.cases shared64_row42
    (Fin.cases shared64_row43
    (Fin.cases shared64_row44
    (Fin.cases shared64_row45
    (Fin.cases shared64_row46
    (Fin.cases shared64_row47
    (Fin.cases shared64_row48
    (Fin.cases shared64_row49
    (Fin.cases shared64_row50
    (Fin.cases shared64_row51
    (Fin.cases shared64_row52
    (Fin.cases shared64_row53
    (Fin.cases shared64_row54
    (Fin.cases shared64_row55
    (Fin.cases shared64_row56
    (Fin.cases shared64_row57
    (Fin.cases shared64_row58
    (Fin.cases shared64_row59
    (Fin.cases shared64_row60
    (Fin.cases shared64_row61
    (Fin.cases shared64_row62
    (Fin.cases shared64_row63
    (Fin.cases shared64_row64
    (Fin.cases shared64_row65
    (Fin.cases shared64_row66
    (Fin.cases shared64_row67
    (Fin.cases shared64_row68
    (Fin.cases shared64_row69
    (Fin.cases shared64_row70
    (Fin.cases shared64_row71
    (Fin.cases shared64_row72
    (Fin.cases shared64_row73
    (Fin.cases shared64_row74
    (Fin.cases shared64_row75
    (Fin.cases shared64_row76
    (Fin.cases shared64_row77
    (Fin.cases shared64_row78
    (Fin.cases shared64_row79
    (Fin.cases shared64_row80
    (Fin.cases shared64_row81
    (Fin.cases shared64_row82
    (Fin.cases shared64_row83
    (Fin.cases shared64_row84
    (Fin.cases shared64_row85
    (Fin.cases shared64_row86
    (Fin.cases shared64_row87
    (Fin.cases shared64_row88
    (Fin.cases shared64_row89
    (Fin.cases shared64_row90
    (Fin.cases shared64_row91
    (Fin.cases shared64_row92
    (Fin.cases shared64_row93
    (Fin.cases shared64_row94
    (Fin.cases shared64_row95
    (Fin.cases shared64_row96
    (Fin.cases shared64_row97
    (Fin.cases shared64_row98
    (Fin.cases shared64_row99
    (Fin.cases shared64_row100
    (Fin.cases shared64_row101
    (Fin.cases shared64_row102
    (Fin.cases shared64_row103
    (Fin.cases shared64_row104
    (Fin.cases shared64_row105
    (Fin.cases shared64_row106
    (Fin.cases shared64_row107
    (Fin.cases shared64_row108
    (Fin.cases shared64_row109
    (Fin.cases shared64_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid39 : checkValid m39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row0 :
    checkProductRow m10 m39 m69 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row1 :
    checkProductRow m10 m39 m69 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row2 :
    checkProductRow m10 m39 m69 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row3 :
    checkProductRow m10 m39 m69 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row4 :
    checkProductRow m10 m39 m69 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row5 :
    checkProductRow m10 m39 m69 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row6 :
    checkProductRow m10 m39 m69 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row7 :
    checkProductRow m10 m39 m69 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row8 :
    checkProductRow m10 m39 m69 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row9 :
    checkProductRow m10 m39 m69 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row10 :
    checkProductRow m10 m39 m69 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row11 :
    checkProductRow m10 m39 m69 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row12 :
    checkProductRow m10 m39 m69 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row13 :
    checkProductRow m10 m39 m69 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row14 :
    checkProductRow m10 m39 m69 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row15 :
    checkProductRow m10 m39 m69 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row16 :
    checkProductRow m10 m39 m69 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row17 :
    checkProductRow m10 m39 m69 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row18 :
    checkProductRow m10 m39 m69 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row19 :
    checkProductRow m10 m39 m69 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row20 :
    checkProductRow m10 m39 m69 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row21 :
    checkProductRow m10 m39 m69 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row22 :
    checkProductRow m10 m39 m69 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row23 :
    checkProductRow m10 m39 m69 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row24 :
    checkProductRow m10 m39 m69 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row25 :
    checkProductRow m10 m39 m69 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row26 :
    checkProductRow m10 m39 m69 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row27 :
    checkProductRow m10 m39 m69 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row28 :
    checkProductRow m10 m39 m69 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row29 :
    checkProductRow m10 m39 m69 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row30 :
    checkProductRow m10 m39 m69 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row31 :
    checkProductRow m10 m39 m69 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row32 :
    checkProductRow m10 m39 m69 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row33 :
    checkProductRow m10 m39 m69 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row34 :
    checkProductRow m10 m39 m69 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row35 :
    checkProductRow m10 m39 m69 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row36 :
    checkProductRow m10 m39 m69 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row37 :
    checkProductRow m10 m39 m69 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row38 :
    checkProductRow m10 m39 m69 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row39 :
    checkProductRow m10 m39 m69 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row40 :
    checkProductRow m10 m39 m69 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row41 :
    checkProductRow m10 m39 m69 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row42 :
    checkProductRow m10 m39 m69 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row43 :
    checkProductRow m10 m39 m69 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row44 :
    checkProductRow m10 m39 m69 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row45 :
    checkProductRow m10 m39 m69 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row46 :
    checkProductRow m10 m39 m69 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row47 :
    checkProductRow m10 m39 m69 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row48 :
    checkProductRow m10 m39 m69 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row49 :
    checkProductRow m10 m39 m69 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row50 :
    checkProductRow m10 m39 m69 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row51 :
    checkProductRow m10 m39 m69 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row52 :
    checkProductRow m10 m39 m69 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row53 :
    checkProductRow m10 m39 m69 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row54 :
    checkProductRow m10 m39 m69 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row55 :
    checkProductRow m10 m39 m69 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row56 :
    checkProductRow m10 m39 m69 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row57 :
    checkProductRow m10 m39 m69 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row58 :
    checkProductRow m10 m39 m69 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row59 :
    checkProductRow m10 m39 m69 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row60 :
    checkProductRow m10 m39 m69 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row61 :
    checkProductRow m10 m39 m69 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row62 :
    checkProductRow m10 m39 m69 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row63 :
    checkProductRow m10 m39 m69 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row64 :
    checkProductRow m10 m39 m69 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row65 :
    checkProductRow m10 m39 m69 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row66 :
    checkProductRow m10 m39 m69 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row67 :
    checkProductRow m10 m39 m69 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row68 :
    checkProductRow m10 m39 m69 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row69 :
    checkProductRow m10 m39 m69 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row70 :
    checkProductRow m10 m39 m69 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row71 :
    checkProductRow m10 m39 m69 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row72 :
    checkProductRow m10 m39 m69 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row73 :
    checkProductRow m10 m39 m69 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row74 :
    checkProductRow m10 m39 m69 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row75 :
    checkProductRow m10 m39 m69 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row76 :
    checkProductRow m10 m39 m69 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row77 :
    checkProductRow m10 m39 m69 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row78 :
    checkProductRow m10 m39 m69 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row79 :
    checkProductRow m10 m39 m69 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row80 :
    checkProductRow m10 m39 m69 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row81 :
    checkProductRow m10 m39 m69 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row82 :
    checkProductRow m10 m39 m69 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row83 :
    checkProductRow m10 m39 m69 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row84 :
    checkProductRow m10 m39 m69 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row85 :
    checkProductRow m10 m39 m69 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row86 :
    checkProductRow m10 m39 m69 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row87 :
    checkProductRow m10 m39 m69 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row88 :
    checkProductRow m10 m39 m69 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row89 :
    checkProductRow m10 m39 m69 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row90 :
    checkProductRow m10 m39 m69 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row91 :
    checkProductRow m10 m39 m69 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row92 :
    checkProductRow m10 m39 m69 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row93 :
    checkProductRow m10 m39 m69 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row94 :
    checkProductRow m10 m39 m69 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row95 :
    checkProductRow m10 m39 m69 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row96 :
    checkProductRow m10 m39 m69 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row97 :
    checkProductRow m10 m39 m69 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row98 :
    checkProductRow m10 m39 m69 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row99 :
    checkProductRow m10 m39 m69 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row100 :
    checkProductRow m10 m39 m69 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row101 :
    checkProductRow m10 m39 m69 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row102 :
    checkProductRow m10 m39 m69 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row103 :
    checkProductRow m10 m39 m69 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row104 :
    checkProductRow m10 m39 m69 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row105 :
    checkProductRow m10 m39 m69 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row106 :
    checkProductRow m10 m39 m69 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row107 :
    checkProductRow m10 m39 m69 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row108 :
    checkProductRow m10 m39 m69 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row109 :
    checkProductRow m10 m39 m69 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared65_row110 :
    checkProductRow m10 m39 m69 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem shared_product65 :
    decode (matrixRows 10) * decode (matrixRows 39) = decode (matrixRows 69) :=
  product_of_checked_rows m10 m39 m69 valid39
    (Fin.cases shared65_row0
    (Fin.cases shared65_row1
    (Fin.cases shared65_row2
    (Fin.cases shared65_row3
    (Fin.cases shared65_row4
    (Fin.cases shared65_row5
    (Fin.cases shared65_row6
    (Fin.cases shared65_row7
    (Fin.cases shared65_row8
    (Fin.cases shared65_row9
    (Fin.cases shared65_row10
    (Fin.cases shared65_row11
    (Fin.cases shared65_row12
    (Fin.cases shared65_row13
    (Fin.cases shared65_row14
    (Fin.cases shared65_row15
    (Fin.cases shared65_row16
    (Fin.cases shared65_row17
    (Fin.cases shared65_row18
    (Fin.cases shared65_row19
    (Fin.cases shared65_row20
    (Fin.cases shared65_row21
    (Fin.cases shared65_row22
    (Fin.cases shared65_row23
    (Fin.cases shared65_row24
    (Fin.cases shared65_row25
    (Fin.cases shared65_row26
    (Fin.cases shared65_row27
    (Fin.cases shared65_row28
    (Fin.cases shared65_row29
    (Fin.cases shared65_row30
    (Fin.cases shared65_row31
    (Fin.cases shared65_row32
    (Fin.cases shared65_row33
    (Fin.cases shared65_row34
    (Fin.cases shared65_row35
    (Fin.cases shared65_row36
    (Fin.cases shared65_row37
    (Fin.cases shared65_row38
    (Fin.cases shared65_row39
    (Fin.cases shared65_row40
    (Fin.cases shared65_row41
    (Fin.cases shared65_row42
    (Fin.cases shared65_row43
    (Fin.cases shared65_row44
    (Fin.cases shared65_row45
    (Fin.cases shared65_row46
    (Fin.cases shared65_row47
    (Fin.cases shared65_row48
    (Fin.cases shared65_row49
    (Fin.cases shared65_row50
    (Fin.cases shared65_row51
    (Fin.cases shared65_row52
    (Fin.cases shared65_row53
    (Fin.cases shared65_row54
    (Fin.cases shared65_row55
    (Fin.cases shared65_row56
    (Fin.cases shared65_row57
    (Fin.cases shared65_row58
    (Fin.cases shared65_row59
    (Fin.cases shared65_row60
    (Fin.cases shared65_row61
    (Fin.cases shared65_row62
    (Fin.cases shared65_row63
    (Fin.cases shared65_row64
    (Fin.cases shared65_row65
    (Fin.cases shared65_row66
    (Fin.cases shared65_row67
    (Fin.cases shared65_row68
    (Fin.cases shared65_row69
    (Fin.cases shared65_row70
    (Fin.cases shared65_row71
    (Fin.cases shared65_row72
    (Fin.cases shared65_row73
    (Fin.cases shared65_row74
    (Fin.cases shared65_row75
    (Fin.cases shared65_row76
    (Fin.cases shared65_row77
    (Fin.cases shared65_row78
    (Fin.cases shared65_row79
    (Fin.cases shared65_row80
    (Fin.cases shared65_row81
    (Fin.cases shared65_row82
    (Fin.cases shared65_row83
    (Fin.cases shared65_row84
    (Fin.cases shared65_row85
    (Fin.cases shared65_row86
    (Fin.cases shared65_row87
    (Fin.cases shared65_row88
    (Fin.cases shared65_row89
    (Fin.cases shared65_row90
    (Fin.cases shared65_row91
    (Fin.cases shared65_row92
    (Fin.cases shared65_row93
    (Fin.cases shared65_row94
    (Fin.cases shared65_row95
    (Fin.cases shared65_row96
    (Fin.cases shared65_row97
    (Fin.cases shared65_row98
    (Fin.cases shared65_row99
    (Fin.cases shared65_row100
    (Fin.cases shared65_row101
    (Fin.cases shared65_row102
    (Fin.cases shared65_row103
    (Fin.cases shared65_row104
    (Fin.cases shared65_row105
    (Fin.cases shared65_row106
    (Fin.cases shared65_row107
    (Fin.cases shared65_row108
    (Fin.cases shared65_row109
    (Fin.cases shared65_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid52 : checkValid m52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row0 :
    checkProductRow m25 m52 m70 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row1 :
    checkProductRow m25 m52 m70 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row2 :
    checkProductRow m25 m52 m70 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row3 :
    checkProductRow m25 m52 m70 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row4 :
    checkProductRow m25 m52 m70 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row5 :
    checkProductRow m25 m52 m70 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row6 :
    checkProductRow m25 m52 m70 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row7 :
    checkProductRow m25 m52 m70 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row8 :
    checkProductRow m25 m52 m70 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row9 :
    checkProductRow m25 m52 m70 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row10 :
    checkProductRow m25 m52 m70 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row11 :
    checkProductRow m25 m52 m70 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row12 :
    checkProductRow m25 m52 m70 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row13 :
    checkProductRow m25 m52 m70 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row14 :
    checkProductRow m25 m52 m70 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row15 :
    checkProductRow m25 m52 m70 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row16 :
    checkProductRow m25 m52 m70 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row17 :
    checkProductRow m25 m52 m70 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row18 :
    checkProductRow m25 m52 m70 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row19 :
    checkProductRow m25 m52 m70 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row20 :
    checkProductRow m25 m52 m70 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row21 :
    checkProductRow m25 m52 m70 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row22 :
    checkProductRow m25 m52 m70 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row23 :
    checkProductRow m25 m52 m70 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row24 :
    checkProductRow m25 m52 m70 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row25 :
    checkProductRow m25 m52 m70 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row26 :
    checkProductRow m25 m52 m70 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row27 :
    checkProductRow m25 m52 m70 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row28 :
    checkProductRow m25 m52 m70 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row29 :
    checkProductRow m25 m52 m70 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row30 :
    checkProductRow m25 m52 m70 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row31 :
    checkProductRow m25 m52 m70 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row32 :
    checkProductRow m25 m52 m70 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row33 :
    checkProductRow m25 m52 m70 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row34 :
    checkProductRow m25 m52 m70 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row35 :
    checkProductRow m25 m52 m70 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row36 :
    checkProductRow m25 m52 m70 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row37 :
    checkProductRow m25 m52 m70 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row38 :
    checkProductRow m25 m52 m70 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row39 :
    checkProductRow m25 m52 m70 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row40 :
    checkProductRow m25 m52 m70 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row41 :
    checkProductRow m25 m52 m70 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row42 :
    checkProductRow m25 m52 m70 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row43 :
    checkProductRow m25 m52 m70 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row44 :
    checkProductRow m25 m52 m70 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row45 :
    checkProductRow m25 m52 m70 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row46 :
    checkProductRow m25 m52 m70 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row47 :
    checkProductRow m25 m52 m70 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row48 :
    checkProductRow m25 m52 m70 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row49 :
    checkProductRow m25 m52 m70 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row50 :
    checkProductRow m25 m52 m70 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row51 :
    checkProductRow m25 m52 m70 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row52 :
    checkProductRow m25 m52 m70 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row53 :
    checkProductRow m25 m52 m70 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row54 :
    checkProductRow m25 m52 m70 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row55 :
    checkProductRow m25 m52 m70 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row56 :
    checkProductRow m25 m52 m70 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row57 :
    checkProductRow m25 m52 m70 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row58 :
    checkProductRow m25 m52 m70 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row59 :
    checkProductRow m25 m52 m70 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row60 :
    checkProductRow m25 m52 m70 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row61 :
    checkProductRow m25 m52 m70 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row62 :
    checkProductRow m25 m52 m70 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row63 :
    checkProductRow m25 m52 m70 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row64 :
    checkProductRow m25 m52 m70 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row65 :
    checkProductRow m25 m52 m70 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row66 :
    checkProductRow m25 m52 m70 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row67 :
    checkProductRow m25 m52 m70 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row68 :
    checkProductRow m25 m52 m70 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row69 :
    checkProductRow m25 m52 m70 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row70 :
    checkProductRow m25 m52 m70 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row71 :
    checkProductRow m25 m52 m70 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row72 :
    checkProductRow m25 m52 m70 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row73 :
    checkProductRow m25 m52 m70 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row74 :
    checkProductRow m25 m52 m70 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row75 :
    checkProductRow m25 m52 m70 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row76 :
    checkProductRow m25 m52 m70 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row77 :
    checkProductRow m25 m52 m70 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row78 :
    checkProductRow m25 m52 m70 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row79 :
    checkProductRow m25 m52 m70 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row80 :
    checkProductRow m25 m52 m70 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row81 :
    checkProductRow m25 m52 m70 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row82 :
    checkProductRow m25 m52 m70 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row83 :
    checkProductRow m25 m52 m70 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row84 :
    checkProductRow m25 m52 m70 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row85 :
    checkProductRow m25 m52 m70 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row86 :
    checkProductRow m25 m52 m70 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row87 :
    checkProductRow m25 m52 m70 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row88 :
    checkProductRow m25 m52 m70 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row89 :
    checkProductRow m25 m52 m70 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row90 :
    checkProductRow m25 m52 m70 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row91 :
    checkProductRow m25 m52 m70 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row92 :
    checkProductRow m25 m52 m70 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row93 :
    checkProductRow m25 m52 m70 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row94 :
    checkProductRow m25 m52 m70 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row95 :
    checkProductRow m25 m52 m70 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row96 :
    checkProductRow m25 m52 m70 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row97 :
    checkProductRow m25 m52 m70 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row98 :
    checkProductRow m25 m52 m70 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row99 :
    checkProductRow m25 m52 m70 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row100 :
    checkProductRow m25 m52 m70 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row101 :
    checkProductRow m25 m52 m70 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row102 :
    checkProductRow m25 m52 m70 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row103 :
    checkProductRow m25 m52 m70 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row104 :
    checkProductRow m25 m52 m70 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row105 :
    checkProductRow m25 m52 m70 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row106 :
    checkProductRow m25 m52 m70 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row107 :
    checkProductRow m25 m52 m70 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row108 :
    checkProductRow m25 m52 m70 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row109 :
    checkProductRow m25 m52 m70 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared66_row110 :
    checkProductRow m25 m52 m70 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem shared_product66 :
    decode (matrixRows 25) * decode (matrixRows 52) = decode (matrixRows 70) :=
  product_of_checked_rows m25 m52 m70 valid52
    (Fin.cases shared66_row0
    (Fin.cases shared66_row1
    (Fin.cases shared66_row2
    (Fin.cases shared66_row3
    (Fin.cases shared66_row4
    (Fin.cases shared66_row5
    (Fin.cases shared66_row6
    (Fin.cases shared66_row7
    (Fin.cases shared66_row8
    (Fin.cases shared66_row9
    (Fin.cases shared66_row10
    (Fin.cases shared66_row11
    (Fin.cases shared66_row12
    (Fin.cases shared66_row13
    (Fin.cases shared66_row14
    (Fin.cases shared66_row15
    (Fin.cases shared66_row16
    (Fin.cases shared66_row17
    (Fin.cases shared66_row18
    (Fin.cases shared66_row19
    (Fin.cases shared66_row20
    (Fin.cases shared66_row21
    (Fin.cases shared66_row22
    (Fin.cases shared66_row23
    (Fin.cases shared66_row24
    (Fin.cases shared66_row25
    (Fin.cases shared66_row26
    (Fin.cases shared66_row27
    (Fin.cases shared66_row28
    (Fin.cases shared66_row29
    (Fin.cases shared66_row30
    (Fin.cases shared66_row31
    (Fin.cases shared66_row32
    (Fin.cases shared66_row33
    (Fin.cases shared66_row34
    (Fin.cases shared66_row35
    (Fin.cases shared66_row36
    (Fin.cases shared66_row37
    (Fin.cases shared66_row38
    (Fin.cases shared66_row39
    (Fin.cases shared66_row40
    (Fin.cases shared66_row41
    (Fin.cases shared66_row42
    (Fin.cases shared66_row43
    (Fin.cases shared66_row44
    (Fin.cases shared66_row45
    (Fin.cases shared66_row46
    (Fin.cases shared66_row47
    (Fin.cases shared66_row48
    (Fin.cases shared66_row49
    (Fin.cases shared66_row50
    (Fin.cases shared66_row51
    (Fin.cases shared66_row52
    (Fin.cases shared66_row53
    (Fin.cases shared66_row54
    (Fin.cases shared66_row55
    (Fin.cases shared66_row56
    (Fin.cases shared66_row57
    (Fin.cases shared66_row58
    (Fin.cases shared66_row59
    (Fin.cases shared66_row60
    (Fin.cases shared66_row61
    (Fin.cases shared66_row62
    (Fin.cases shared66_row63
    (Fin.cases shared66_row64
    (Fin.cases shared66_row65
    (Fin.cases shared66_row66
    (Fin.cases shared66_row67
    (Fin.cases shared66_row68
    (Fin.cases shared66_row69
    (Fin.cases shared66_row70
    (Fin.cases shared66_row71
    (Fin.cases shared66_row72
    (Fin.cases shared66_row73
    (Fin.cases shared66_row74
    (Fin.cases shared66_row75
    (Fin.cases shared66_row76
    (Fin.cases shared66_row77
    (Fin.cases shared66_row78
    (Fin.cases shared66_row79
    (Fin.cases shared66_row80
    (Fin.cases shared66_row81
    (Fin.cases shared66_row82
    (Fin.cases shared66_row83
    (Fin.cases shared66_row84
    (Fin.cases shared66_row85
    (Fin.cases shared66_row86
    (Fin.cases shared66_row87
    (Fin.cases shared66_row88
    (Fin.cases shared66_row89
    (Fin.cases shared66_row90
    (Fin.cases shared66_row91
    (Fin.cases shared66_row92
    (Fin.cases shared66_row93
    (Fin.cases shared66_row94
    (Fin.cases shared66_row95
    (Fin.cases shared66_row96
    (Fin.cases shared66_row97
    (Fin.cases shared66_row98
    (Fin.cases shared66_row99
    (Fin.cases shared66_row100
    (Fin.cases shared66_row101
    (Fin.cases shared66_row102
    (Fin.cases shared66_row103
    (Fin.cases shared66_row104
    (Fin.cases shared66_row105
    (Fin.cases shared66_row106
    (Fin.cases shared66_row107
    (Fin.cases shared66_row108
    (Fin.cases shared66_row109
    (Fin.cases shared66_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid32 : checkValid m32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row0 :
    checkProductRow m40 m32 m71 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row1 :
    checkProductRow m40 m32 m71 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row2 :
    checkProductRow m40 m32 m71 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row3 :
    checkProductRow m40 m32 m71 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row4 :
    checkProductRow m40 m32 m71 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row5 :
    checkProductRow m40 m32 m71 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row6 :
    checkProductRow m40 m32 m71 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row7 :
    checkProductRow m40 m32 m71 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row8 :
    checkProductRow m40 m32 m71 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row9 :
    checkProductRow m40 m32 m71 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row10 :
    checkProductRow m40 m32 m71 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row11 :
    checkProductRow m40 m32 m71 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row12 :
    checkProductRow m40 m32 m71 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row13 :
    checkProductRow m40 m32 m71 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row14 :
    checkProductRow m40 m32 m71 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row15 :
    checkProductRow m40 m32 m71 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row16 :
    checkProductRow m40 m32 m71 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row17 :
    checkProductRow m40 m32 m71 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row18 :
    checkProductRow m40 m32 m71 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row19 :
    checkProductRow m40 m32 m71 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row20 :
    checkProductRow m40 m32 m71 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row21 :
    checkProductRow m40 m32 m71 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row22 :
    checkProductRow m40 m32 m71 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row23 :
    checkProductRow m40 m32 m71 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row24 :
    checkProductRow m40 m32 m71 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row25 :
    checkProductRow m40 m32 m71 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row26 :
    checkProductRow m40 m32 m71 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row27 :
    checkProductRow m40 m32 m71 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row28 :
    checkProductRow m40 m32 m71 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row29 :
    checkProductRow m40 m32 m71 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row30 :
    checkProductRow m40 m32 m71 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row31 :
    checkProductRow m40 m32 m71 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row32 :
    checkProductRow m40 m32 m71 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row33 :
    checkProductRow m40 m32 m71 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row34 :
    checkProductRow m40 m32 m71 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row35 :
    checkProductRow m40 m32 m71 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row36 :
    checkProductRow m40 m32 m71 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row37 :
    checkProductRow m40 m32 m71 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row38 :
    checkProductRow m40 m32 m71 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row39 :
    checkProductRow m40 m32 m71 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row40 :
    checkProductRow m40 m32 m71 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row41 :
    checkProductRow m40 m32 m71 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row42 :
    checkProductRow m40 m32 m71 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row43 :
    checkProductRow m40 m32 m71 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row44 :
    checkProductRow m40 m32 m71 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row45 :
    checkProductRow m40 m32 m71 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row46 :
    checkProductRow m40 m32 m71 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row47 :
    checkProductRow m40 m32 m71 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row48 :
    checkProductRow m40 m32 m71 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row49 :
    checkProductRow m40 m32 m71 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row50 :
    checkProductRow m40 m32 m71 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row51 :
    checkProductRow m40 m32 m71 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row52 :
    checkProductRow m40 m32 m71 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row53 :
    checkProductRow m40 m32 m71 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row54 :
    checkProductRow m40 m32 m71 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row55 :
    checkProductRow m40 m32 m71 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row56 :
    checkProductRow m40 m32 m71 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row57 :
    checkProductRow m40 m32 m71 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row58 :
    checkProductRow m40 m32 m71 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row59 :
    checkProductRow m40 m32 m71 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row60 :
    checkProductRow m40 m32 m71 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row61 :
    checkProductRow m40 m32 m71 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row62 :
    checkProductRow m40 m32 m71 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row63 :
    checkProductRow m40 m32 m71 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row64 :
    checkProductRow m40 m32 m71 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row65 :
    checkProductRow m40 m32 m71 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row66 :
    checkProductRow m40 m32 m71 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row67 :
    checkProductRow m40 m32 m71 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row68 :
    checkProductRow m40 m32 m71 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row69 :
    checkProductRow m40 m32 m71 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row70 :
    checkProductRow m40 m32 m71 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row71 :
    checkProductRow m40 m32 m71 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row72 :
    checkProductRow m40 m32 m71 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row73 :
    checkProductRow m40 m32 m71 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row74 :
    checkProductRow m40 m32 m71 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row75 :
    checkProductRow m40 m32 m71 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row76 :
    checkProductRow m40 m32 m71 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row77 :
    checkProductRow m40 m32 m71 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row78 :
    checkProductRow m40 m32 m71 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row79 :
    checkProductRow m40 m32 m71 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row80 :
    checkProductRow m40 m32 m71 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row81 :
    checkProductRow m40 m32 m71 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row82 :
    checkProductRow m40 m32 m71 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row83 :
    checkProductRow m40 m32 m71 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row84 :
    checkProductRow m40 m32 m71 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row85 :
    checkProductRow m40 m32 m71 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row86 :
    checkProductRow m40 m32 m71 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row87 :
    checkProductRow m40 m32 m71 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row88 :
    checkProductRow m40 m32 m71 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row89 :
    checkProductRow m40 m32 m71 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row90 :
    checkProductRow m40 m32 m71 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row91 :
    checkProductRow m40 m32 m71 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row92 :
    checkProductRow m40 m32 m71 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row93 :
    checkProductRow m40 m32 m71 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row94 :
    checkProductRow m40 m32 m71 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row95 :
    checkProductRow m40 m32 m71 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row96 :
    checkProductRow m40 m32 m71 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row97 :
    checkProductRow m40 m32 m71 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row98 :
    checkProductRow m40 m32 m71 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row99 :
    checkProductRow m40 m32 m71 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row100 :
    checkProductRow m40 m32 m71 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row101 :
    checkProductRow m40 m32 m71 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row102 :
    checkProductRow m40 m32 m71 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row103 :
    checkProductRow m40 m32 m71 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row104 :
    checkProductRow m40 m32 m71 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row105 :
    checkProductRow m40 m32 m71 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row106 :
    checkProductRow m40 m32 m71 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row107 :
    checkProductRow m40 m32 m71 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row108 :
    checkProductRow m40 m32 m71 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row109 :
    checkProductRow m40 m32 m71 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared67_row110 :
    checkProductRow m40 m32 m71 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem shared_product67 :
    decode (matrixRows 40) * decode (matrixRows 32) = decode (matrixRows 71) :=
  product_of_checked_rows m40 m32 m71 valid32
    (Fin.cases shared67_row0
    (Fin.cases shared67_row1
    (Fin.cases shared67_row2
    (Fin.cases shared67_row3
    (Fin.cases shared67_row4
    (Fin.cases shared67_row5
    (Fin.cases shared67_row6
    (Fin.cases shared67_row7
    (Fin.cases shared67_row8
    (Fin.cases shared67_row9
    (Fin.cases shared67_row10
    (Fin.cases shared67_row11
    (Fin.cases shared67_row12
    (Fin.cases shared67_row13
    (Fin.cases shared67_row14
    (Fin.cases shared67_row15
    (Fin.cases shared67_row16
    (Fin.cases shared67_row17
    (Fin.cases shared67_row18
    (Fin.cases shared67_row19
    (Fin.cases shared67_row20
    (Fin.cases shared67_row21
    (Fin.cases shared67_row22
    (Fin.cases shared67_row23
    (Fin.cases shared67_row24
    (Fin.cases shared67_row25
    (Fin.cases shared67_row26
    (Fin.cases shared67_row27
    (Fin.cases shared67_row28
    (Fin.cases shared67_row29
    (Fin.cases shared67_row30
    (Fin.cases shared67_row31
    (Fin.cases shared67_row32
    (Fin.cases shared67_row33
    (Fin.cases shared67_row34
    (Fin.cases shared67_row35
    (Fin.cases shared67_row36
    (Fin.cases shared67_row37
    (Fin.cases shared67_row38
    (Fin.cases shared67_row39
    (Fin.cases shared67_row40
    (Fin.cases shared67_row41
    (Fin.cases shared67_row42
    (Fin.cases shared67_row43
    (Fin.cases shared67_row44
    (Fin.cases shared67_row45
    (Fin.cases shared67_row46
    (Fin.cases shared67_row47
    (Fin.cases shared67_row48
    (Fin.cases shared67_row49
    (Fin.cases shared67_row50
    (Fin.cases shared67_row51
    (Fin.cases shared67_row52
    (Fin.cases shared67_row53
    (Fin.cases shared67_row54
    (Fin.cases shared67_row55
    (Fin.cases shared67_row56
    (Fin.cases shared67_row57
    (Fin.cases shared67_row58
    (Fin.cases shared67_row59
    (Fin.cases shared67_row60
    (Fin.cases shared67_row61
    (Fin.cases shared67_row62
    (Fin.cases shared67_row63
    (Fin.cases shared67_row64
    (Fin.cases shared67_row65
    (Fin.cases shared67_row66
    (Fin.cases shared67_row67
    (Fin.cases shared67_row68
    (Fin.cases shared67_row69
    (Fin.cases shared67_row70
    (Fin.cases shared67_row71
    (Fin.cases shared67_row72
    (Fin.cases shared67_row73
    (Fin.cases shared67_row74
    (Fin.cases shared67_row75
    (Fin.cases shared67_row76
    (Fin.cases shared67_row77
    (Fin.cases shared67_row78
    (Fin.cases shared67_row79
    (Fin.cases shared67_row80
    (Fin.cases shared67_row81
    (Fin.cases shared67_row82
    (Fin.cases shared67_row83
    (Fin.cases shared67_row84
    (Fin.cases shared67_row85
    (Fin.cases shared67_row86
    (Fin.cases shared67_row87
    (Fin.cases shared67_row88
    (Fin.cases shared67_row89
    (Fin.cases shared67_row90
    (Fin.cases shared67_row91
    (Fin.cases shared67_row92
    (Fin.cases shared67_row93
    (Fin.cases shared67_row94
    (Fin.cases shared67_row95
    (Fin.cases shared67_row96
    (Fin.cases shared67_row97
    (Fin.cases shared67_row98
    (Fin.cases shared67_row99
    (Fin.cases shared67_row100
    (Fin.cases shared67_row101
    (Fin.cases shared67_row102
    (Fin.cases shared67_row103
    (Fin.cases shared67_row104
    (Fin.cases shared67_row105
    (Fin.cases shared67_row106
    (Fin.cases shared67_row107
    (Fin.cases shared67_row108
    (Fin.cases shared67_row109
    (Fin.cases shared67_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.RelationCertificate
