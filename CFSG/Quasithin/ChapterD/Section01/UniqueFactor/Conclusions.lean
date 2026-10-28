module

public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Stellmacher.ElementaryAbelianMaxDefs
public import Theory.GroupTheory.PResidual.Defs

/-!
# The requested conclusion of the unique-factor source branch

This is a target specification, not an additional hypothesis for D.1.4.
The reduced FF-module is an actual G₂-invariant elementary subgroup of U,
with its faithful conjugation action. Centers, residuals and Thompson
subgroups retain the original ambient embeddings. The Sylow clause is
separate because it uses the earlier solvable odd-residual implication.

Source: Aschbacher--Smith, D.1.4(2), printed pp.175--176; the later A₃-block
addendum is not used in the classification route considered here.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.UniqueFactor
open Subgroup Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The actual reduced FF-submodule required in D.1.4(2). -/
def ContainsReducedFF (H U : Subgroup G) : Prop :=
  ∃ W : Subgroup G, W ≤ U ∧ W ≤ H ∧
    ∃ hW : H ≤ normalizer (W : Set G),
    ∃ hE : IsElementaryAbelian 2 W,
      letI := hE
      pCore 2 (internalActionImage H W hW) = ⊥ ∧
      Representation.BinaryOffender.IsFFModule (imageRepresentation H W hW)

/-- All nonsolvable-independent structural clauses used in the selected source
route. This record is only a conclusion to be constructed by the source proof. -/
structure StructuralConclusion (G₁ G₂ T V : Subgroup G) : Prop where
  intersection_normalized : G₂ ≤ normalizer ((twoCoreIn G₁ ⊓ twoCoreIn G₂ : Subgroup G) : Set G)
  span_elementary : IsElementaryAbelian 2 (conjugateSpan G₂ V)
  commutator_central : ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ ≤
    (center (twoCoreIn G₂)).map (twoCoreIn G₂).subtype
  residual_thompson : (pResidual 2 G₂).map G₂.subtype =
    ⁅(pResidual 2 G₂).map G₂.subtype, elementaryAbelianMaxJ (twoCoreIn G₁)⁆
  thompson_eq : elementaryAbelianMaxJ T = elementaryAbelianMaxJ (twoCoreIn G₁)
  contains_reduced_ff : ContainsReducedFF G₂ (conjugateSpan G₂ V)

end CFSG.Quasithin.ChapterD.UniqueFactor
