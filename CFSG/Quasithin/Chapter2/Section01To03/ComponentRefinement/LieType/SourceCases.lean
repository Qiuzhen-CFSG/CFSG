module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Endpoints
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry

/-!
# Source inputs and the binary surviving conclusion

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(a–c), printed pp.501–502, and 2.3.9(7), printed pp.525–526.

`SimpleLieModel` is precisely the union of Theorem C(3) and C(4), using
the concrete catalogue and its field conventions. In particular, U₄ and U₅
do not occur, and the small symplectic, G₂ and Tits derived groups remain
separate from their full groups.

`SourceModelCases` retains the model and inner-action consequences needed
from 1.1.5(3)(a–c). In case (c), only the model is needed: the additional
transposition assertion may be forgotten. No parabolic, block obstruction,
diagram action or intersection conclusion is assumed. The central-cover
branch retains the entire O₂(L), with no bound on its order.

`CaseG` includes an actual PSL₄(2) equivalence, a nontrivial action on its
transported subspace types by N_S(L), and the literal projection-centralizer
intersection. The equivalence alone would not establish this conclusion.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType

open Subgroup ClassificationModels ChapterA.Section02

/-- The actual characteristic-two simple models in Theorem C(3–4). -/
def SimpleLieModel (K : Type*) [Group K] : Prop :=
  IsBenderModel K ∨
    (∃ f : ℕ, IsTheoremCRankTwoModel K f) ∨
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL K n 2

variable {G : Type*} [Group G]

/-- The model and action inputs supplied by 1.1.5(3)(a–c).
The transposition action in (c) is unnecessary for this refinement. -/
inductive SourceModelCases (L : Subgroup G) (z : G) : Prop
  | simple_lie (simple : IsSimpleGroup L) (model : SimpleLieModel L)
      (inner : ∃ t : L, IsConjugationProjection L z t)
  | central_two_cover (central : center L = pCore 2 L) (nontrivial : pCore 2 L ≠ ⊥)
      (model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨
        IsG2At (L ⧸ pCore 2 L) 4)
      (inner : ∃ t : L, IsConjugationProjection L z t)
  | alternating_six (model : Nonempty (L ≃* alternatingGroup (Fin 6)))
  | triple_six (model : IsTripleAlternatingSixCover L)

/-- All three assertions of 2.3.9(7)(g), with S viewed inside G. -/
def CaseG (L M S : Subgroup G) (z : G) : Prop :=
  ∃ e : L ≃* Binary.PSL 4, Binary.NontrivialDynkinAction e S ∧
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧
      L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType

end
