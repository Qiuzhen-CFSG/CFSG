module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The remaining M₂₄ local configuration

The source uses an overgroup with a normal two-group and quotient S₃ × L₃(2).
`LocalQuotient` uses the binary special linear group; the explicit projective
comparison below identifies it with the source's projective group.

`LocalOvergroups` and `SylowNormalizerControl` are separate, unproved task
contracts on the fixed Witt-design carrier. The first requires placement of
an arbitrary permuting pair and an actual quotient homomorphism. The second
controls the conjugators implementing pair automorphisms. Neither contract
assumes an invariant subgroup of R or its Frattini quotient.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Table 5.3e, the local subgroup
E₆₄.N(3B), with N(3B) = S₃ × L₃(2). No splitting is required.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

/-- The concrete quotient model in the M₂₄ local calculation. -/
abbrev LocalQuotient :=
  Equiv.Perm (Fin 3) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

/-- The matrix factor is the projective group appearing in the source. -/
noncomputable def localQuotientEquiv :
    LocalQuotient ≃* (Equiv.Perm (Fin 3) × PSL(3, ZMod 2)) :=
  MulEquiv.prodCongr (MulEquiv.refl _) Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two

/-- Placement and an actual quotient with two-group kernel, still to be proved
for every source pair. This is not a local classification theorem. -/
def LocalOvergroups : Prop :=
  ∀ (S : Sylow 2 Sporadic.Mathieu.M24) (R : Subgroup Sporadic.Mathieu.M24),
    PairInput S R → ∃ H : Subgroup Sporadic.Mathieu.M24,
      (S : Subgroup Sporadic.Mathieu.M24) ≤ H ∧ R ≤ H ∧
      ∃ f : H →* LocalQuotient, Function.Surjective f ∧ IsPGroup 2 f.ker

/-- The independent Sylow-normalizer calculation used by the assembly. -/
def SylowNormalizerControl : Prop :=
  ∀ S : Sylow 2 Sporadic.Mathieu.M24,
    normalizer (S : Set Sporadic.Mathieu.M24) ≤ (S : Subgroup Sporadic.Mathieu.M24)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction
