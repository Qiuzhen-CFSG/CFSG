module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart0
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart1
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart2
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart3
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart4
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart5
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart6
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart7
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart8
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart9
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart10
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart11
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart12
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart13
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart14
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart15
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart16
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart17
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart18
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart19
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart20
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart21
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart22
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart23
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart24
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart25
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart26
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart27
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSharedPart28

/-!
# Certified shared subwords for the Lyons local presentation

All 113 products in `sharedSpec` hold for the fixed candidate matrices.
The supporting modules check each packed product row by kernel reduction;
finite case analysis assembles those products into the universal contract.
No seed or relator-batch certificate is needed here.

Source data and reproducible row checks: `Atlas111LocalRelationSource/`.
-/

namespace Lyons.RelationCertificate

set_option maxRecDepth 10000 in
private theorem allFin113 {P : Fin 113 → Prop}
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
    (h22 : P 22)
    (h23 : P 23)
    (h24 : P 24)
    (h25 : P 25)
    (h26 : P 26)
    (h27 : P 27)
    (h28 : P 28)
    (h29 : P 29)
    (h30 : P 30)
    (h31 : P 31)
    (h32 : P 32)
    (h33 : P 33)
    (h34 : P 34)
    (h35 : P 35)
    (h36 : P 36)
    (h37 : P 37)
    (h38 : P 38)
    (h39 : P 39)
    (h40 : P 40)
    (h41 : P 41)
    (h42 : P 42)
    (h43 : P 43)
    (h44 : P 44)
    (h45 : P 45)
    (h46 : P 46)
    (h47 : P 47)
    (h48 : P 48)
    (h49 : P 49)
    (h50 : P 50)
    (h51 : P 51)
    (h52 : P 52)
    (h53 : P 53)
    (h54 : P 54)
    (h55 : P 55)
    (h56 : P 56)
    (h57 : P 57)
    (h58 : P 58)
    (h59 : P 59)
    (h60 : P 60)
    (h61 : P 61)
    (h62 : P 62)
    (h63 : P 63)
    (h64 : P 64)
    (h65 : P 65)
    (h66 : P 66)
    (h67 : P 67)
    (h68 : P 68)
    (h69 : P 69)
    (h70 : P 70)
    (h71 : P 71)
    (h72 : P 72)
    (h73 : P 73)
    (h74 : P 74)
    (h75 : P 75)
    (h76 : P 76)
    (h77 : P 77)
    (h78 : P 78)
    (h79 : P 79)
    (h80 : P 80)
    (h81 : P 81)
    (h82 : P 82)
    (h83 : P 83)
    (h84 : P 84)
    (h85 : P 85)
    (h86 : P 86)
    (h87 : P 87)
    (h88 : P 88)
    (h89 : P 89)
    (h90 : P 90)
    (h91 : P 91)
    (h92 : P 92)
    (h93 : P 93)
    (h94 : P 94)
    (h95 : P 95)
    (h96 : P 96)
    (h97 : P 97)
    (h98 : P 98)
    (h99 : P 99)
    (h100 : P 100)
    (h101 : P 101)
    (h102 : P 102)
    (h103 : P 103)
    (h104 : P 104)
    (h105 : P 105)
    (h106 : P 106)
    (h107 : P 107)
    (h108 : P 108)
    (h109 : P 109)
    (h110 : P 110)
    (h111 : P 111)
    (h112 : P 112)
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
    (Fin.cases h22
    (Fin.cases h23
    (Fin.cases h24
    (Fin.cases h25
    (Fin.cases h26
    (Fin.cases h27
    (Fin.cases h28
    (Fin.cases h29
    (Fin.cases h30
    (Fin.cases h31
    (Fin.cases h32
    (Fin.cases h33
    (Fin.cases h34
    (Fin.cases h35
    (Fin.cases h36
    (Fin.cases h37
    (Fin.cases h38
    (Fin.cases h39
    (Fin.cases h40
    (Fin.cases h41
    (Fin.cases h42
    (Fin.cases h43
    (Fin.cases h44
    (Fin.cases h45
    (Fin.cases h46
    (Fin.cases h47
    (Fin.cases h48
    (Fin.cases h49
    (Fin.cases h50
    (Fin.cases h51
    (Fin.cases h52
    (Fin.cases h53
    (Fin.cases h54
    (Fin.cases h55
    (Fin.cases h56
    (Fin.cases h57
    (Fin.cases h58
    (Fin.cases h59
    (Fin.cases h60
    (Fin.cases h61
    (Fin.cases h62
    (Fin.cases h63
    (Fin.cases h64
    (Fin.cases h65
    (Fin.cases h66
    (Fin.cases h67
    (Fin.cases h68
    (Fin.cases h69
    (Fin.cases h70
    (Fin.cases h71
    (Fin.cases h72
    (Fin.cases h73
    (Fin.cases h74
    (Fin.cases h75
    (Fin.cases h76
    (Fin.cases h77
    (Fin.cases h78
    (Fin.cases h79
    (Fin.cases h80
    (Fin.cases h81
    (Fin.cases h82
    (Fin.cases h83
    (Fin.cases h84
    (Fin.cases h85
    (Fin.cases h86
    (Fin.cases h87
    (Fin.cases h88
    (Fin.cases h89
    (Fin.cases h90
    (Fin.cases h91
    (Fin.cases h92
    (Fin.cases h93
    (Fin.cases h94
    (Fin.cases h95
    (Fin.cases h96
    (Fin.cases h97
    (Fin.cases h98
    (Fin.cases h99
    (Fin.cases h100
    (Fin.cases h101
    (Fin.cases h102
    (Fin.cases h103
    (Fin.cases h104
    (Fin.cases h105
    (Fin.cases h106
    (Fin.cases h107
    (Fin.cases h108
    (Fin.cases h109
    (Fin.cases h110
    (Fin.cases h111
    (Fin.cases h112
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Every shared-subword multiplication contract is satisfied by the candidate matrices. -/
public theorem sharedIdentities : SharedIdentities :=
  allFin113 (P := fun i => let e := sharedSpec i;
    decode (matrixRows e.1) * decode (matrixRows e.2.1) = decode (matrixRows e.2.2))
    shared_product0 shared_product1 shared_product2 shared_product3
    shared_product4 shared_product5 shared_product6 shared_product7
    shared_product8 shared_product9 shared_product10 shared_product11
    shared_product12 shared_product13 shared_product14 shared_product15
    shared_product16 shared_product17 shared_product18 shared_product19
    shared_product20 shared_product21 shared_product22 shared_product23
    shared_product24 shared_product25 shared_product26 shared_product27
    shared_product28 shared_product29 shared_product30 shared_product31
    shared_product32 shared_product33 shared_product34 shared_product35
    shared_product36 shared_product37 shared_product38 shared_product39
    shared_product40 shared_product41 shared_product42 shared_product43
    shared_product44 shared_product45 shared_product46 shared_product47
    shared_product48 shared_product49 shared_product50 shared_product51
    shared_product52 shared_product53 shared_product54 shared_product55
    shared_product56 shared_product57 shared_product58 shared_product59
    shared_product60 shared_product61 shared_product62 shared_product63
    shared_product64 shared_product65 shared_product66 shared_product67
    shared_product68 shared_product69 shared_product70 shared_product71
    shared_product72 shared_product73 shared_product74 shared_product75
    shared_product76 shared_product77 shared_product78 shared_product79
    shared_product80 shared_product81 shared_product82 shared_product83
    shared_product84 shared_product85 shared_product86 shared_product87
    shared_product88 shared_product89 shared_product90 shared_product91
    shared_product92 shared_product93 shared_product94 shared_product95
    shared_product96 shared_product97 shared_product98 shared_product99
    shared_product100 shared_product101 shared_product102 shared_product103
    shared_product104 shared_product105 shared_product106 shared_product107
    shared_product108 shared_product109 shared_product110 shared_product111
    shared_product112

end Lyons.RelationCertificate
