module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Contracts

/-!
# The literal eight-point residual model

The local group is the centralizer of `(01)(23)` in A₈, and its residual is
O² of that group, embedded into A₈. The distinguished elements are the
existing marks, without a change of coordinates. These definitions isolate
the finite-model calculations from the ambient transfer argument.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38 (point labels shifted to 0,…,7).
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel
open Subgroup

/-- The actual local centralizer in A₈. -/
abbrev C := Centralizer t8

/-- Its two-residual, embedded by the actual subgroup inclusion. -/
def R : Subgroup Eight := (pResidual 2 C).map C.subtype

/-- The first marked involution, regarded as an element of the local group. -/
def z : C := ⟨z8, mem_centralizer_singleton_iff.mpr z8_commutes_t8.eq⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel
end
