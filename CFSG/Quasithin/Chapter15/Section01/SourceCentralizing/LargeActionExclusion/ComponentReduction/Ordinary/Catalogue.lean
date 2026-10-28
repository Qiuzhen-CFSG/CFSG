module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.BinaryModels

/-!
# The ordinary quotient list after the source rank-one exclusions

These are exactly the quotient models still needed from 15.1.20(3c--e)
after 15.1.21 removes (3a--b). We keep HS and Ru: the exchanged-source
consumer excludes them directly, without needing their earlier elimination
in the proof of 15.1.22. Every alternative is an actual isomorphism predicate
on the original quotient L/O₂(L).

This is a conclusion interface, not a classification theorem. Derivation
from the full source hypotheses remains with the earlier 15.1.20--22
catalogue producer. KnownSimple membership alone does not imply this list.

Source: Aschbacher--Smith 15.1.20(3), 15.1.21, printed pp.1094--1098.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

/-- The literal quotient alternatives of ordinary source rows (3c--e),
including the two sporadic cases removed later in the printed proof. -/
def OrdinaryPostRankOneModel (Q : Type*) [Group Q] : Prop :=
  SmallOrdinaryModel Q ∨ SmallBinaryOrdinaryModel Q ∨
    Nonempty (Q ≃* Sporadic.LeechRelated.HS.Carrier) ∨
    Nonempty (Q ≃* Held.He) ∨ Nonempty (Q ≃* Rudvalis.Model) ∨
    Nonempty (Q ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
