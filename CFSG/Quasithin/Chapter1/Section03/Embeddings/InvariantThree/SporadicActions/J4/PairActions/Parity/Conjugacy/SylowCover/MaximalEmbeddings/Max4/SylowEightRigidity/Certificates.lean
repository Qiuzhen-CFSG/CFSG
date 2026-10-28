module

public import Theory.GroupTheory.CentralizerLowerCentralCard
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model

/-!
# Concrete obligations for the max4 Sylow normal-eight calculation

The reference group is the existing subgroup of the actual J₄ matrix carrier
constructed from the max1 kernel and the four certified quotient-Sylow words.
It is not a new abstract group identified by its order. Two independent inputs
remain: an actual isomorphism with a Sylow of literal max4, and a complete
normal-eight catalogue with three distinct centralizer lower-central orders.

The expected catalogue can be searched in the elementary third center of order
sixteen. Saved GAP computations predict the orders below, but neither that
center calculation nor these certificates is asserted by this module.

Source context: Kleidman--Wilson, *The maximal subgroups of J₄* (1988),
pp.484--510; the application in Aschbacher--Smith, `refs/quasithin.pdf`,
printed p.511/PDF p.528. Literal max4 words and their provenance are in
`SymmetricLinear.Model`. These are sufficient computational contracts, not
claims that the source proves them by projection.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- The already defined, literal max1 matrix two-subgroup of order 2^21. -/
noncomputable abbrev SylowEightModel := Janko4.OuterReduction.OddIndex.twoSubgroup

/-- One local Sylow of literal max4 is actually isomorphic to the reference group. -/
def Max4SylowEightModelComparison : Prop :=
  ∃ P : Sylow 2 Janko4.LocalStructure.SymmetricLinear.max4Subgroup,
    Nonempty (P ≃* SylowEightModel)

/-- Predicted orders of the third lower-central terms, in catalogue order. -/
def normalEightCentralizerOrder (i : Fin 3) : ℕ := ![128, 1024, 512] i

/-- Concrete coverage and the three numerical certificates still to be proved.
The lower-central index is two, since its zeroth term is the whole group. -/
def Max4SylowEightCentralizerCertificates : Prop :=
  ∃ family : Fin 3 → Subgroup SylowEightModel,
    (∀ A : Subgroup SylowEightModel, A.Normal → IsElementaryAbelian 2 A →
      Nat.card A = 8 → A ≤ Subgroup.upperCentralSeries SylowEightModel 3 →
        ∃ i, A = family i) ∧
    (∀ i, Subgroup.centralizerLowerCentralCard (family i) 2 = normalEightCentralizerOrder i)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
