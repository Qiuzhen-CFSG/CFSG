module

public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The core-square clause in the exceptional-cover table

In I.2.2(5c), (6b) and (7c), X is the two-residual O²(C_K(u)),
not the two-core. The square roots in (5c) and (6b) lie in O₂(X).
We embed both subgroups back into K, so the coset and square equations
use the literal central quotient map and multiplication in K.

These are shared definitions, not assertions of the source table.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, I.2.2,
printed pp.409–410 / PDF pp.420–421, checked against the PDF.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
open Subgroup Theory.GroupTheory
variable {K : Type*} [Group K]

/-- The actual O₂(O²(C_K(u))), embedded in K. -/
def centralizerCore (u : K) : Subgroup K :=
  (pCore 2 (centralizerTwoResidual u)).map (centralizerTwoResidual u).subtype

/-- The unique element of uZ(K) which is a square in the indicated core. -/
def HasUniqueCoreSquareLift (u : K) : Prop :=
  ∃! v : K, QuotientGroup.mk' (center K) v = QuotientGroup.mk' (center K) u ∧
    ∃ x ∈ centralizerCore u, x ^ 2 = v

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
