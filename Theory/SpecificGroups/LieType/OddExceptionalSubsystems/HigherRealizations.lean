module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.E8Properness
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.Words

/-!
# Higher exceptional realizations of the folded E6 subgroup

The marked signed E7 and E8 generator products are defined on the literal
matrix covers. The E8 generated subgroup has proper image under the literal
central projection over every field. The final embeddings still require
the matrix-word comparison with the source folded subgroup, and E7 requires
its own projected properness argument. No map out of the entire adjoint E6
group is postulated.

Sources: Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`,
and GLS3 §2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem

namespace TwistedE6.FoldedSubsystem.HigherRealizations

attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

/-- Conditional E7 assembly. Both the word comparison and projected properness
remain explicit mathematical obligations; only centerlessness is supplied by
the eventual F4 identification owner. -/
def e7ProperEmbeddingOfWordKernels
    (hk : (sourceWord F).ker = (e7Word F).ker)
    (hp : (e7FoldedProjection F).range ≠ ⊤)
    (hc : Subgroup.center (splitSubgroup F) = ⊥) :
    ExceptionalSplit.ProperEmbedding (splitSubgroup F) (ExceptionalSplit.E7 F) where
  hom := (ExceptionalSplit.projection typeE7RootPairing typeE7RootPairing_base F).comp
    (e7CoverMapOfWordKernels F hk)
  injective := centralProjection_injective _ (e7CoverMapOfWordKernels_injective F hk) hc
  proper := by
    rw [MonoidHom.range_comp, e7_range_eq F _ (e7CoverMapOfWordKernels_f4Simple F hk)]
    simpa only [e7FoldedProjection, MonoidHom.range_comp, Subgroup.range_subtype] using hp

/-- E8 assembly uses the proved centralizer obstruction, leaving only the
matrix-word comparison and the allowed centerlessness premise. -/
def e8ProperEmbeddingOfWordKernels
    (hk : (sourceWord F).ker = (e8Word F).ker)
    (hc : Subgroup.center (splitSubgroup F) = ⊥) :
    ExceptionalSplit.ProperEmbedding (splitSubgroup F) (ExceptionalSplit.E8 F) :=
  e8ProperEmbeddingOfMarkedHom F (e8CoverMapOfWordKernels F hk)
    (e8CoverMapOfWordKernels_injective F hk) (e8CoverMapOfWordKernels_f4Simple F hk) hc

end TwistedE6.FoldedSubsystem.HigherRealizations
