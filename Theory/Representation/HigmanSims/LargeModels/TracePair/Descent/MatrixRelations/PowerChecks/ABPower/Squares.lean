module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Squares.CSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Squares.DSquare

/-!
# The two squaring links in the literal HS eleventh-power certificate

`Squares.c_square_eq_d` and `Squares.d_square_eq_e` establish CC = D and
DD = E for the unchanged packed matrices over `Four`. All 896 row images
are certified by coordinate images, addition, and multiplication by omega.
These supply exactly the two squaring premises of
`ABPower.pow_eleven_eq_one_of_products`; the parent retains the separate
CE = F, FF = G, and GC = I obligations.

Source: relator 2, `(x*y)^11`, of `Descent/source/HSG1-P1.M` and the
ATLAS matrices HSG1-f4r896aB0. See `Squares/source/README.md` for attribution,
certificate generation and complete-module measurements.
-/
