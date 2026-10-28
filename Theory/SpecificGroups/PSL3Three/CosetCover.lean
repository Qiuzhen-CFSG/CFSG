module

public import Theory.SpecificGroups.PSL3Three.CosetCover.Node00
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node01
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node02
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node03
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node04
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node05
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node06
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node07
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node08
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node09
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node10
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node11
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node12
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node13
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node14
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node15
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node16
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node17
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node18
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node19
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node20
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node21
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node22
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node23
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node24
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node25
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node26
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node27
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node28
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node29
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node30
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node31
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node32
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node33
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node34
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node35
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node36
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node37
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node38
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node39
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node40
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node41
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node42
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node43
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node44
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node45
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node46
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node47
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node48
public import Theory.SpecificGroups.PSL3Three.CosetCover.Node49

/-!
# Certified right-coset covers for the fixed SL₃(3) subgroups

For each of the fifty proper nodes from `RepresentativeBounds`, this module
provides a finite list of actual determinant-one matrices and proves that its
right cosets cover SL₃(3). The lists have 28,526 rows in total. Neither the
counts nor the external enumeration are premises: each row's product with each
of the four ambient generators has a kernel-checked subgroup-word factorization.
The identity row and the ambient generation theorem then imply coverage by
`RightCosetTable.sound`.

Node numbers and matrix codes are those of `RepresentativeBounds`; row zero is
the identity, followed by the remaining representatives in increasing code order.
The counts are lengths of covers; no assertion of distinctness is needed here.
`CosetCover/Generate.py` regenerates the untrusted node data from the fixed lists.

Source: the elementary coset-table criterion in `SubgroupEnumeration`, applied
to the concrete matrices underlying GLS III, Theorem 6.5.3.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration

open Theory.GroupTheory.SubgroupEnumeration

/-- Number of certified right-coset representatives for each fixed proper node. -/
@[expose] public def cosetCount : Fin 50 → Nat :=
  ![5616, 2808, 1872, 1872, 1404, 1404, 936, 936, 936, 936, 702, 702, 702, 624, 624, 624, 468, 468, 432, 351, 312, 312, 312, 312, 312, 234, 234, 208, 156, 156, 156, 156, 144, 117, 104, 104, 104, 78, 78, 78, 78, 78, 78, 52, 39, 39, 26, 26, 13, 13]

/-- Actual matrices, with the same row numbering as the checked transition tables. -/
@[expose] public def cosetRepresentative : (i : Fin 50) → Fin (cosetCount i) → SL :=
  Fin.cases Cosets00.rep <|
  Fin.cases Cosets01.rep <|
  Fin.cases Cosets02.rep <|
  Fin.cases Cosets03.rep <|
  Fin.cases Cosets04.rep <|
  Fin.cases Cosets05.rep <|
  Fin.cases Cosets06.rep <|
  Fin.cases Cosets07.rep <|
  Fin.cases Cosets08.rep <|
  Fin.cases Cosets09.rep <|
  Fin.cases Cosets10.rep <|
  Fin.cases Cosets11.rep <|
  Fin.cases Cosets12.rep <|
  Fin.cases Cosets13.rep <|
  Fin.cases Cosets14.rep <|
  Fin.cases Cosets15.rep <|
  Fin.cases Cosets16.rep <|
  Fin.cases Cosets17.rep <|
  Fin.cases Cosets18.rep <|
  Fin.cases Cosets19.rep <|
  Fin.cases Cosets20.rep <|
  Fin.cases Cosets21.rep <|
  Fin.cases Cosets22.rep <|
  Fin.cases Cosets23.rep <|
  Fin.cases Cosets24.rep <|
  Fin.cases Cosets25.rep <|
  Fin.cases Cosets26.rep <|
  Fin.cases Cosets27.rep <|
  Fin.cases Cosets28.rep <|
  Fin.cases Cosets29.rep <|
  Fin.cases Cosets30.rep <|
  Fin.cases Cosets31.rep <|
  Fin.cases Cosets32.rep <|
  Fin.cases Cosets33.rep <|
  Fin.cases Cosets34.rep <|
  Fin.cases Cosets35.rep <|
  Fin.cases Cosets36.rep <|
  Fin.cases Cosets37.rep <|
  Fin.cases Cosets38.rep <|
  Fin.cases Cosets39.rep <|
  Fin.cases Cosets40.rep <|
  Fin.cases Cosets41.rep <|
  Fin.cases Cosets42.rep <|
  Fin.cases Cosets43.rep <|
  Fin.cases Cosets44.rep <|
  Fin.cases Cosets45.rep <|
  Fin.cases Cosets46.rep <|
  Fin.cases Cosets47.rep <|
  Fin.cases Cosets48.rep <|
  Fin.cases Cosets49.rep <|
  fun j => Fin.elim0 j

/-- Every matrix factors as a member of the fixed subgroup times a listed row. -/
public theorem rightCosetCover (i : Fin 50) :
    RightCosetCover (properNode i) (cosetRepresentative i) := by
  fin_cases i
  · exact Cosets00.cover
  · exact Cosets01.cover
  · exact Cosets02.cover
  · exact Cosets03.cover
  · exact Cosets04.cover
  · exact Cosets05.cover
  · exact Cosets06.cover
  · exact Cosets07.cover
  · exact Cosets08.cover
  · exact Cosets09.cover
  · exact Cosets10.cover
  · exact Cosets11.cover
  · exact Cosets12.cover
  · exact Cosets13.cover
  · exact Cosets14.cover
  · exact Cosets15.cover
  · exact Cosets16.cover
  · exact Cosets17.cover
  · exact Cosets18.cover
  · exact Cosets19.cover
  · exact Cosets20.cover
  · exact Cosets21.cover
  · exact Cosets22.cover
  · exact Cosets23.cover
  · exact Cosets24.cover
  · exact Cosets25.cover
  · exact Cosets26.cover
  · exact Cosets27.cover
  · exact Cosets28.cover
  · exact Cosets29.cover
  · exact Cosets30.cover
  · exact Cosets31.cover
  · exact Cosets32.cover
  · exact Cosets33.cover
  · exact Cosets34.cover
  · exact Cosets35.cover
  · exact Cosets36.cover
  · exact Cosets37.cover
  · exact Cosets38.cover
  · exact Cosets39.cover
  · exact Cosets40.cover
  · exact Cosets41.cover
  · exact Cosets42.cover
  · exact Cosets43.cover
  · exact Cosets44.cover
  · exact Cosets45.cover
  · exact Cosets46.cover
  · exact Cosets47.cover
  · exact Cosets48.cover
  · exact Cosets49.cover

end Matrix.PSL3Three.CertifiedEnumeration
