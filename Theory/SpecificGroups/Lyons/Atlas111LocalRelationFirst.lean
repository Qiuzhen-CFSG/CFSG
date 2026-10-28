module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationFirstProduct0
public import Theory.SpecificGroups.Lyons.RelationFirstProducts.Batch01
public import Theory.SpecificGroups.Lyons.RelationFirstProducts.Batch11
public import Theory.SpecificGroups.Lyons.RelationFirstProducts.Batch21
public import Theory.SpecificGroups.Lyons.RelationFirstProducts.Batch31
public import Theory.SpecificGroups.Lyons.RelationFirstProducts.Batch41
public import Theory.SpecificGroups.Lyons.RelationFirstProducts.Batch51

namespace Lyons.RelationCertificate

set_option Elab.async false

private theorem allFin55 {P : Fin 55 → Prop}
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
    : ∀ i, P i := by
  exact (Fin.cases h0
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
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Every first-subword multiplication contract is satisfied by the candidate matrices. -/
public theorem firstIdentities : FirstIdentities :=
  allFin55 (P := fun i => let e := firstSpec i;
    decode (matrixRows e.1) * decode (matrixRows e.2.1) = decode (matrixRows e.2.2))
    (by simpa [firstSpec, matrixRows] using first_product0)
    (by simpa [firstSpec, matrixRows] using first_product1)
    (by simpa [firstSpec, matrixRows] using first_product2)
    (by simpa [firstSpec, matrixRows] using first_product3)
    (by simpa [firstSpec, matrixRows] using first_product4)
    (by simpa [firstSpec, matrixRows] using first_product5)
    (by simpa [firstSpec, matrixRows] using first_product6)
    (by simpa [firstSpec, matrixRows] using first_product7)
    (by simpa [firstSpec, matrixRows] using first_product8)
    (by simpa [firstSpec, matrixRows] using first_product9)
    (by simpa [firstSpec, matrixRows] using first_product10)
    (by simpa [firstSpec, matrixRows] using first_product11)
    (by simpa [firstSpec, matrixRows] using first_product12)
    (by simpa [firstSpec, matrixRows] using first_product13)
    (by simpa [firstSpec, matrixRows] using first_product14)
    (by simpa [firstSpec, matrixRows] using first_product15)
    (by simpa [firstSpec, matrixRows] using first_product16)
    (by simpa [firstSpec, matrixRows] using first_product17)
    (by simpa [firstSpec, matrixRows] using first_product18)
    (by simpa [firstSpec, matrixRows] using first_product19)
    (by simpa [firstSpec, matrixRows] using first_product20)
    (by simpa [firstSpec, matrixRows] using first_product21)
    (by simpa [firstSpec, matrixRows] using first_product22)
    (by simpa [firstSpec, matrixRows] using first_product23)
    (by simpa [firstSpec, matrixRows] using first_product24)
    (by simpa [firstSpec, matrixRows] using first_product25)
    (by simpa [firstSpec, matrixRows] using first_product26)
    (by simpa [firstSpec, matrixRows] using first_product27)
    (by simpa [firstSpec, matrixRows] using first_product28)
    (by simpa [firstSpec, matrixRows] using first_product29)
    (by simpa [firstSpec, matrixRows] using first_product30)
    (by simpa [firstSpec, matrixRows] using first_product31)
    (by simpa [firstSpec, matrixRows] using first_product32)
    (by simpa [firstSpec, matrixRows] using first_product33)
    (by simpa [firstSpec, matrixRows] using first_product34)
    (by simpa [firstSpec, matrixRows] using first_product35)
    (by simpa [firstSpec, matrixRows] using first_product36)
    (by simpa [firstSpec, matrixRows] using first_product37)
    (by simpa [firstSpec, matrixRows] using first_product38)
    (by simpa [firstSpec, matrixRows] using first_product39)
    (by simpa [firstSpec, matrixRows] using first_product40)
    (by simpa [firstSpec, matrixRows] using first_product41)
    (by simpa [firstSpec, matrixRows] using first_product42)
    (by simpa [firstSpec, matrixRows] using first_product43)
    (by simpa [firstSpec, matrixRows] using first_product44)
    (by simpa [firstSpec, matrixRows] using first_product45)
    (by simpa [firstSpec, matrixRows] using first_product46)
    (by simpa [firstSpec, matrixRows] using first_product47)
    (by simpa [firstSpec, matrixRows] using first_product48)
    (by simpa [firstSpec, matrixRows] using first_product49)
    (by simpa [firstSpec, matrixRows] using first_product50)
    (by simpa [firstSpec, matrixRows] using first_product51)
    (by simpa [firstSpec, matrixRows] using first_product52)
    (by simpa [firstSpec, matrixRows] using first_product53)
    (by simpa [firstSpec, matrixRows] using first_product54)

end Lyons.RelationCertificate
