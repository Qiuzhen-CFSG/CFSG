module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Collection

/-!
# Small word data for the Rudvalis special core

The eleven words are exactly Max4Words.generator, in the already certified
fourteen-letter coordinates. The three central words are prospective marked
basis elements. Squares and commutators are encoded as three-bit masks in
that marked order. Relations proves the identities; data alone assert none.

The untrusted masks were discovered by GAP in the original ATLAS model,
with the inverse point-action convention retained from LocalCover.Data.
Source: Aschbacher--Smith I.2.2(7), pp.412--413; GLS3 Table 5.3r, pp.291--292.
-/

namespace Rudvalis.CoveringIncidence.Max4Special
open SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate
open Collection

@[expose] public def word : Fin 11 → List (Fin 14) :=
  ![[1, 2, 3, 4, 6, 7, 10, 11, 12, 13],
    [0, 1, 4, 6, 8, 10, 11],
    [8, 9],
    [0, 2, 5, 6, 7, 9, 10, 11, 12, 13],
    [0, 2, 3, 4, 5, 6, 10],
    [4, 5, 11, 12],
    [4, 5, 9, 10, 11, 12, 13],
    [6],
    [6, 7, 8, 9, 11, 13],
    [13],
    [12, 13]]

@[expose] public def centerWord : Fin 3 → List (Fin 14) :=
  ![[12, 13], [13], [6, 7, 8, 9, 11, 13]]

@[expose] public def centralWord (n : Fin 8) : List (Fin 14) :=
  (if n.val % 2 = 1 then centerWord 0 else []) ++
  (if n.val / 2 % 2 = 1 then centerWord 1 else []) ++
  (if n.val / 4 % 2 = 1 then centerWord 2 else [])

@[expose] public def centralValue (n : Fin 8) : Model := eval (centralWord n)

@[expose] public def squareCode : Fin 11 → Fin 8 :=
  ![4, 3, 0, 3, 5, 0, 0, 0, 0, 0, 0]

@[expose] public def commutatorCode : Fin 11 → Fin 11 → Fin 8 :=
  ![![0, 3, 4, 0, 2, 3, 4, 3, 0, 0, 0],
    ![3, 0, 5, 5, 2, 1, 4, 6, 0, 0, 0],
    ![4, 5, 0, 0, 4, 7, 6, 0, 0, 0, 0],
    ![0, 5, 0, 0, 3, 1, 3, 4, 0, 0, 0],
    ![2, 2, 4, 3, 0, 5, 7, 5, 0, 0, 0],
    ![3, 1, 7, 1, 5, 0, 0, 1, 0, 0, 0],
    ![4, 4, 6, 3, 7, 0, 0, 1, 0, 0, 0],
    ![3, 6, 0, 4, 5, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

@[simp] public theorem centralValue_zero : centralValue 0 = 1 := rfl

end Rudvalis.CoveringIncidence.Max4Special
