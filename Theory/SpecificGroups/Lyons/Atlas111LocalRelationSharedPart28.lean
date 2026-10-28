module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts

/-!
# Shared-subword products 112–112 for the local presentation

Each row equality is checked by kernel reduction. The proved packed-row
soundness theorem converts the checks to ordinary matrix multiplication.
Source data and reproducible generation: `Atlas111LocalRelationSource/`.
-/

namespace Lyons.RelationCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem valid19 : checkValid m19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row0 :
    checkProductRow m73 m19 m115 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row1 :
    checkProductRow m73 m19 m115 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row2 :
    checkProductRow m73 m19 m115 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row3 :
    checkProductRow m73 m19 m115 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row4 :
    checkProductRow m73 m19 m115 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row5 :
    checkProductRow m73 m19 m115 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row6 :
    checkProductRow m73 m19 m115 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row7 :
    checkProductRow m73 m19 m115 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row8 :
    checkProductRow m73 m19 m115 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row9 :
    checkProductRow m73 m19 m115 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row10 :
    checkProductRow m73 m19 m115 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row11 :
    checkProductRow m73 m19 m115 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row12 :
    checkProductRow m73 m19 m115 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row13 :
    checkProductRow m73 m19 m115 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row14 :
    checkProductRow m73 m19 m115 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row15 :
    checkProductRow m73 m19 m115 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row16 :
    checkProductRow m73 m19 m115 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row17 :
    checkProductRow m73 m19 m115 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row18 :
    checkProductRow m73 m19 m115 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row19 :
    checkProductRow m73 m19 m115 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row20 :
    checkProductRow m73 m19 m115 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row21 :
    checkProductRow m73 m19 m115 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row22 :
    checkProductRow m73 m19 m115 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row23 :
    checkProductRow m73 m19 m115 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row24 :
    checkProductRow m73 m19 m115 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row25 :
    checkProductRow m73 m19 m115 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row26 :
    checkProductRow m73 m19 m115 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row27 :
    checkProductRow m73 m19 m115 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row28 :
    checkProductRow m73 m19 m115 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row29 :
    checkProductRow m73 m19 m115 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row30 :
    checkProductRow m73 m19 m115 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row31 :
    checkProductRow m73 m19 m115 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row32 :
    checkProductRow m73 m19 m115 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row33 :
    checkProductRow m73 m19 m115 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row34 :
    checkProductRow m73 m19 m115 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row35 :
    checkProductRow m73 m19 m115 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row36 :
    checkProductRow m73 m19 m115 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row37 :
    checkProductRow m73 m19 m115 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row38 :
    checkProductRow m73 m19 m115 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row39 :
    checkProductRow m73 m19 m115 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row40 :
    checkProductRow m73 m19 m115 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row41 :
    checkProductRow m73 m19 m115 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row42 :
    checkProductRow m73 m19 m115 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row43 :
    checkProductRow m73 m19 m115 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row44 :
    checkProductRow m73 m19 m115 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row45 :
    checkProductRow m73 m19 m115 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row46 :
    checkProductRow m73 m19 m115 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row47 :
    checkProductRow m73 m19 m115 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row48 :
    checkProductRow m73 m19 m115 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row49 :
    checkProductRow m73 m19 m115 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row50 :
    checkProductRow m73 m19 m115 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row51 :
    checkProductRow m73 m19 m115 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row52 :
    checkProductRow m73 m19 m115 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row53 :
    checkProductRow m73 m19 m115 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row54 :
    checkProductRow m73 m19 m115 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row55 :
    checkProductRow m73 m19 m115 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row56 :
    checkProductRow m73 m19 m115 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row57 :
    checkProductRow m73 m19 m115 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row58 :
    checkProductRow m73 m19 m115 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row59 :
    checkProductRow m73 m19 m115 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row60 :
    checkProductRow m73 m19 m115 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row61 :
    checkProductRow m73 m19 m115 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row62 :
    checkProductRow m73 m19 m115 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row63 :
    checkProductRow m73 m19 m115 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row64 :
    checkProductRow m73 m19 m115 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row65 :
    checkProductRow m73 m19 m115 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row66 :
    checkProductRow m73 m19 m115 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row67 :
    checkProductRow m73 m19 m115 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row68 :
    checkProductRow m73 m19 m115 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row69 :
    checkProductRow m73 m19 m115 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row70 :
    checkProductRow m73 m19 m115 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row71 :
    checkProductRow m73 m19 m115 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row72 :
    checkProductRow m73 m19 m115 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row73 :
    checkProductRow m73 m19 m115 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row74 :
    checkProductRow m73 m19 m115 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row75 :
    checkProductRow m73 m19 m115 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row76 :
    checkProductRow m73 m19 m115 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row77 :
    checkProductRow m73 m19 m115 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row78 :
    checkProductRow m73 m19 m115 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row79 :
    checkProductRow m73 m19 m115 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row80 :
    checkProductRow m73 m19 m115 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row81 :
    checkProductRow m73 m19 m115 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row82 :
    checkProductRow m73 m19 m115 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row83 :
    checkProductRow m73 m19 m115 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row84 :
    checkProductRow m73 m19 m115 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row85 :
    checkProductRow m73 m19 m115 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row86 :
    checkProductRow m73 m19 m115 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row87 :
    checkProductRow m73 m19 m115 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row88 :
    checkProductRow m73 m19 m115 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row89 :
    checkProductRow m73 m19 m115 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row90 :
    checkProductRow m73 m19 m115 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row91 :
    checkProductRow m73 m19 m115 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row92 :
    checkProductRow m73 m19 m115 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row93 :
    checkProductRow m73 m19 m115 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row94 :
    checkProductRow m73 m19 m115 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row95 :
    checkProductRow m73 m19 m115 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row96 :
    checkProductRow m73 m19 m115 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row97 :
    checkProductRow m73 m19 m115 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row98 :
    checkProductRow m73 m19 m115 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row99 :
    checkProductRow m73 m19 m115 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row100 :
    checkProductRow m73 m19 m115 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row101 :
    checkProductRow m73 m19 m115 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row102 :
    checkProductRow m73 m19 m115 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row103 :
    checkProductRow m73 m19 m115 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row104 :
    checkProductRow m73 m19 m115 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row105 :
    checkProductRow m73 m19 m115 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row106 :
    checkProductRow m73 m19 m115 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row107 :
    checkProductRow m73 m19 m115 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row108 :
    checkProductRow m73 m19 m115 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row109 :
    checkProductRow m73 m19 m115 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem shared112_row110 :
    checkProductRow m73 m19 m115 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
public theorem shared_product112 :
    decode (matrixRows 73) * decode (matrixRows 19) = decode (matrixRows 115) :=
  product_of_checked_rows m73 m19 m115 valid19
    (Fin.cases shared112_row0
    (Fin.cases shared112_row1
    (Fin.cases shared112_row2
    (Fin.cases shared112_row3
    (Fin.cases shared112_row4
    (Fin.cases shared112_row5
    (Fin.cases shared112_row6
    (Fin.cases shared112_row7
    (Fin.cases shared112_row8
    (Fin.cases shared112_row9
    (Fin.cases shared112_row10
    (Fin.cases shared112_row11
    (Fin.cases shared112_row12
    (Fin.cases shared112_row13
    (Fin.cases shared112_row14
    (Fin.cases shared112_row15
    (Fin.cases shared112_row16
    (Fin.cases shared112_row17
    (Fin.cases shared112_row18
    (Fin.cases shared112_row19
    (Fin.cases shared112_row20
    (Fin.cases shared112_row21
    (Fin.cases shared112_row22
    (Fin.cases shared112_row23
    (Fin.cases shared112_row24
    (Fin.cases shared112_row25
    (Fin.cases shared112_row26
    (Fin.cases shared112_row27
    (Fin.cases shared112_row28
    (Fin.cases shared112_row29
    (Fin.cases shared112_row30
    (Fin.cases shared112_row31
    (Fin.cases shared112_row32
    (Fin.cases shared112_row33
    (Fin.cases shared112_row34
    (Fin.cases shared112_row35
    (Fin.cases shared112_row36
    (Fin.cases shared112_row37
    (Fin.cases shared112_row38
    (Fin.cases shared112_row39
    (Fin.cases shared112_row40
    (Fin.cases shared112_row41
    (Fin.cases shared112_row42
    (Fin.cases shared112_row43
    (Fin.cases shared112_row44
    (Fin.cases shared112_row45
    (Fin.cases shared112_row46
    (Fin.cases shared112_row47
    (Fin.cases shared112_row48
    (Fin.cases shared112_row49
    (Fin.cases shared112_row50
    (Fin.cases shared112_row51
    (Fin.cases shared112_row52
    (Fin.cases shared112_row53
    (Fin.cases shared112_row54
    (Fin.cases shared112_row55
    (Fin.cases shared112_row56
    (Fin.cases shared112_row57
    (Fin.cases shared112_row58
    (Fin.cases shared112_row59
    (Fin.cases shared112_row60
    (Fin.cases shared112_row61
    (Fin.cases shared112_row62
    (Fin.cases shared112_row63
    (Fin.cases shared112_row64
    (Fin.cases shared112_row65
    (Fin.cases shared112_row66
    (Fin.cases shared112_row67
    (Fin.cases shared112_row68
    (Fin.cases shared112_row69
    (Fin.cases shared112_row70
    (Fin.cases shared112_row71
    (Fin.cases shared112_row72
    (Fin.cases shared112_row73
    (Fin.cases shared112_row74
    (Fin.cases shared112_row75
    (Fin.cases shared112_row76
    (Fin.cases shared112_row77
    (Fin.cases shared112_row78
    (Fin.cases shared112_row79
    (Fin.cases shared112_row80
    (Fin.cases shared112_row81
    (Fin.cases shared112_row82
    (Fin.cases shared112_row83
    (Fin.cases shared112_row84
    (Fin.cases shared112_row85
    (Fin.cases shared112_row86
    (Fin.cases shared112_row87
    (Fin.cases shared112_row88
    (Fin.cases shared112_row89
    (Fin.cases shared112_row90
    (Fin.cases shared112_row91
    (Fin.cases shared112_row92
    (Fin.cases shared112_row93
    (Fin.cases shared112_row94
    (Fin.cases shared112_row95
    (Fin.cases shared112_row96
    (Fin.cases shared112_row97
    (Fin.cases shared112_row98
    (Fin.cases shared112_row99
    (Fin.cases shared112_row100
    (Fin.cases shared112_row101
    (Fin.cases shared112_row102
    (Fin.cases shared112_row103
    (Fin.cases shared112_row104
    (Fin.cases shared112_row105
    (Fin.cases shared112_row106
    (Fin.cases shared112_row107
    (Fin.cases shared112_row108
    (Fin.cases shared112_row109
    (Fin.cases shared112_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.RelationCertificate
