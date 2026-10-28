module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Construction.Normalizer

/-!
# Output required from the intrinsic root calculations

`RootCalculation` is a shared output contract, not an existence theorem or
an additional source assumption. Its producers must construct the root from
an actual model equivalence and identify it with `residualRoot L X`. Here X
will be the literal `modifiedCentralizerResidual L u`. The source normalizer,
faithful representation, TI, mover and cover deductions are proved separately
and are deliberately absent from this contract.

The final source assembly remains incomplete until every applicable model
row constructs this output. Source: Aschbacher--Smith, combined manuscript
(1 March 2004), proof of Lemma 16.5.13, printed pp.1201--1202.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
open Subgroup
variable {G : Type*} [Group G]

/-- The three literal relative residual descriptions on printed p.1201.
The family-specific producer must choose the correct case: P∞ off PSL₃;
C_P(Z) in odd degree; O³(C_P(Z)) in even degree. -/
def ResidualDescription (L X : Subgroup G) : Prop :=
  let Z := residualRoot L X
  let P := relativeNormalizer L Z
  X = (solvableResidual P).map P.subtype ∨
    X = P ⊓ centralizer (Z : Set G) ∨
    X = (pResidual 3 (P ⊓ centralizer (Z : Set G) : Subgroup G)).map
      (P ⊓ centralizer (Z : Set G) : Subgroup G).subtype

/-- Output of the model calculation. This structure does not assert that
such a root calculation exists for a source configuration. -/
structure RootCalculation (T : Sylow 2 G) (L X : Subgroup G) (n : ℕ) : Prop where
  degree : 1 < n
  root_nontrivial : residualRoot L X ≠ ⊥
  root_le_residual : residualRoot L X ≤ X
  root_elementary : IsElementaryAbelian 2 (residualRoot L X)
  commuting_elementary : IsElementaryAbelian 2 (commutingSylow T L)
  space_eq : space T X = residualRoot L X ⊔ commutingSylow T L
  residual_description : ResidualDescription L X
  image_cyclic : IsCyclic (inducedActor (space T X) X
    (relativeNormalizer L (residualRoot L X)))
  image_card : Nat.card (inducedActor (space T X) X
    (relativeNormalizer L (residualRoot L X))) = 2 ^ n - 1
  fixed_group : space T X ⊓ centralizer
    (relativeNormalizer L (residualRoot L X) : Set G) = commutingSylow T L
  commutator_eq : ⁅space T X, relativeNormalizer L (residualRoot L X)⁆ = residualRoot L X
  root_transitive : ∀ v ∈ residualRoot L X, v ≠ 1 →
    ∀ w ∈ residualRoot L X, w ≠ 1 →
      ∃ p ∈ relativeNormalizer L (residualRoot L X), MulAut.conj p v = w
  normalizer_index : ((T : Subgroup G) ⊓ normalizer (X : Set G)).relIndex T ≤ 2
  diagram_exception : (T : Subgroup G) ≤ normalizer (X : Set G) ∨ center L = ⊥

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
