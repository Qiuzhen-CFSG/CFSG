module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.Certificates

/-!
# Ambient normalizer obligations for the three J₄ Sylow eights

The reference group is the literal matrix subgroup `OddIndex.twoSubgroup`.
The separate normal-eight catalogue distinguishes its three candidates by
the orders 128, 1024, and 512 of the third lower-central terms of their
intrinsic centralizers. That catalogue does not compute ambient normalizers.

The sufficient remaining calculation below bounds each ambient normalizer
by a proper conjugate of the literal ATLAS max4 subgroup, or places it
strictly inside another proper subgroup. Strictness in the second case is
essential: a mere containment in a different maximal subgroup would not
exclude a maximal normal-eight overgroup. No row is asserted here, and no
uniqueness of normal eights in a Sylow group is assumed.

Source context: Aschbacher–Smith A.3.12, printed pp.47–48, cites Aschbacher's
*Overgroups of Sylow subgroups in sporadic groups* (1986). The concrete
maximal-subgroup reference is Kleidman–Wilson (1988), pp.484–510. These
are sufficient certificate contracts for the literal matrix carrier, not
substitutes for that source analysis or its model comparisons.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

open Subgroup Janko4.LocalStructure.SymmetricLinear
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- An ambient bound retaining the actual subgroup embedding. The second
alternative certifies that the normalizer cannot contain a maximal subgroup. -/
def EightNormalizerAlternative (U : Subgroup Janko4.Model) : Prop :=
  (∃ g : Janko4.Model,
    normalizer (U : Set Janko4.Model) ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom) ∨
  ∃ H : Subgroup Janko4.Model, normalizer (U : Set Janko4.Model) < H ∧ H ≠ ⊤

/-- The remaining finite normalizer calculation, with a single catalogue row
as explicit input. It can be proved independently of exhaustive coverage. -/
def SylowEightNormalizerRows : Prop :=
  ∀ A : Subgroup SylowEightModel, A.Normal → IsElementaryAbelian 2 A →
    Nat.card A = 8 → A ≤ Subgroup.upperCentralSeries SylowEightModel 3 →
    ∀ i : Fin 3, centralizerLowerCentralCard A 2 = normalEightCentralizerOrder i →
      EightNormalizerAlternative (A.map SylowEightModel.subtype)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
