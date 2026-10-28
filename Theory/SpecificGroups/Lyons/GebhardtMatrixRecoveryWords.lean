module

public import Theory.SpecificGroups.Lyons.GebhardtMatrixRealizationSetup

/-!
# Recovering the ambient Lyons generators

These explicit words in the five Sims–Gebhardt generators recover the original
ATLAS matrix pair in numerical computations over GF(5). To find them, we used
the orbit of a 7-dimensional subspace preserved by the four local matrices.
An orbit collision reduces each ambient generator to a local residual; its
action on projective points supplies a short factorization in `a,b,c,d`.
Both lifted factorizations were checked on the full 111-dimensional matrices.

The definitions provide the recovery fields for `WordData`. Independent kernel
certification of the matrix identities belongs to `WordCertificate`; no such
certificate is asserted here. See `GebhardtMatrixSource/recovery-words.md` for
the two residual factorizations and the numerical validation procedure.

Sources: V. Gebhardt, "Two Short Presentations for Lyons' Sporadic Simple
Group", Experimental Mathematics 9 (2000), 333–338, Section 3B, for the five
generators; `Atlas111Source/README.md` for the exact ATLAS matrix pair.
The recovery words themselves were computed from these concrete matrices.
-/

namespace Lyons.Gebhardt.MatrixRealization
@[expose] public section

/-- Explicit recovery word for the first ambient ATLAS generator. -/
def recoverA : FreeGroup Alphabet :=
  word "ccacDCAbbDCCaCdaCCaCACBcACabbcBacAzdBzcbCDZbCA"

/-- Explicit recovery word for the second ambient ATLAS generator. -/
def recoverB : FreeGroup Alphabet :=
  word "BCAcabcAcacBBabaBABDCACAbABDaaCACAccDCBDCBzbbdcbCZdCbCZA"

end
end Lyons.Gebhardt.MatrixRealization
