module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction

/-!
# The two projective order-nine action obligations

The actual projection SU₃ → PSU₃ partitions elementary order-nine subgroups
according to whether their full preimage is abelian. Each contract asks for
reducibility of every two-subgroup of the full pair automizer, including outer
automorphisms. Both retain the Sylow-product hypothesis. Simplicity is inherited
from the source component; it need not be certified afresh for the matrix model.

These definitions state the remaining model obligations, not proved exclusions.
The matrix field has order p² and its stored conjugation is x ↦ x^p. In particular,
a projective elementary subgroup is not assumed to have abelian lifts to SU₃.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); compare A.3.21(c), printed pp.55–56.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary

/-- The remaining full pair-action obligation when the special-unitary
preimage of the projective elementary subgroup is abelian. -/
def AbelianLiftReducibility (p : ℕ) : Prop :=
  ∀ {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E),
    IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
    Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
    ∀ (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      IsElementaryAbelian 3 U → Nat.card U = 9 →
      IsMulCommutative (U.comap J.specialToProjective) →
      (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (T : Set _) =
        (T : Set _) * (U : Set _) → PairReducible (T : Subgroup _) U

/-- The remaining full pair-action obligation when the special-unitary
preimage is nonabelian. This branch also requires invariant subgroups. -/
def NonabelianLiftReducibility (p : ℕ) : Prop :=
  ∀ {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E),
    IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
    Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
    ∀ (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      IsElementaryAbelian 3 U → Nat.card U = 9 →
      ¬ IsMulCommutative (U.comap J.specialToProjective) →
      (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (T : Set _) =
        (T : Set _) * (U : Set _) → PairReducible (T : Subgroup _) U

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary
