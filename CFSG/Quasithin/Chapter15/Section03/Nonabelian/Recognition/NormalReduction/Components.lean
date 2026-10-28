module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Components.Structure
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Components.Embeddings
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Components.ConstituentDimension
public import Theory.Quasithin.Rank

/-!
# Conditional nonsolvable minimal-normal reduction for the literal actor

For the faithful irreducible action of `H/O₂(H)` on `U/Z`, a nonsolvable
minimal normal subgroup is perfect, equals its genuine two-residual, and
is a direct product of one or two isomorphic nonabelian simple groups.
Every irreducible submodule for this subgroup has binary dimension at least
three. The direct-power equivalence retains the component inclusions:
`Components.componentEmbedding` and `Components.componentEquiv` identify
its commuting, normal, simple coordinate subgroups inside the minimal
normal subgroup, without incorrectly asserting their normality in `H/O₂(H)`.

These are the nonsolvable-case reductions used by both branches of the
proof of 15.3.58. The parent must prove nonsolvability and supply the earlier
source irreducibility and strong-quasithin hypotheses. This module does
not claim the final recognition as `Aut(L₃(2))`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1149.
-/

@[expose] public section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

variable {G : Type*} [Group G] [Finite G]

/-- Odd prime ranks descend through the actual two-core quotient. -/
theorem actor_stronglyQuasithin (Z : Subgroup G)
    (hH : IsStronglyQuasithin (centralizerH Z)) :
    IsStronglyQuasithin (ActorQuotient Z) := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho
    (pCore 2 (centralizerH Z)) pCore_isPGroup).trans (hH p hp ho)

/-- The two-core quotient retains the complete input K-group class. -/
theorem actor_sqtk (Z : Subgroup G) {C : GroupClass}
    (hH : IsSQTK C (centralizerH Z)) : IsSQTK C (ActorQuotient Z) :=
  ⟨actor_stronglyQuasithin Z hH.stronglyQuasithin,
    hH.isKGroup.quotient (pCore 2 (centralizerH Z))⟩

variable (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The nonsolvable minimal-normal reduction on the literal source quotient
and its faithful binary action, with no assumed component count or constituent bound. -/
theorem actor_nonsolvable_minimalNormal_reduction
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hρ : (actorRepresentation Z ZS hkernel).IsIrreducible)
    (hqt : IsStronglyQuasithin (centralizerH Z))
    (K : Subgroup (ActorQuotient Z)) (hK : IsMinimalNormal K)
    (hns : ¬ Group.IsSolvable K) :
    Group.IsPerfect K ∧ pResidual 2 K = ⊤ ∧
      (∃ S : Subgroup K, IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧
        ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nonempty (K ≃* (Fin n → S))) ∧
      ∀ A : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype),
        A.toRepresentation.IsIrreducible →
          3 ≤ Module.finrank (ZMod 2) A.toSubmodule := by
  refine ⟨hK.isPerfect_of_not_isSolvable K hns, hK.twoResidual_eq_top K hns,
    hK.exists_simple_power K hns ((actor_stronglyQuasithin Z hqt).subgroup K), ?_⟩
  exact fun A hA => hK.constituent_finrank_ge_three (actorRepresentation Z ZS hkernel)
    hρ (actorRepresentation_injective Z ZS hkernel) K hns A hA

/-- The actual simple factor belongs to the full K-group class supplied for
the actor quotient. Both the carrier and its direct-power isomorphism are retained. -/
theorem actor_simple_power_of_sqtk {C : GroupClass}
    (hqt : IsSQTK C (centralizerH Z))
    (K : Subgroup (ActorQuotient Z)) (hK : IsMinimalNormal K)
    (hns : ¬ Group.IsSolvable K) :
    ∃ S : Subgroup K, IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧ C S ∧
      ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nonempty (K ≃* (Fin n → S)) :=
  hK.exists_simple_power_of_sqtk (actor_sqtk Z hqt) K hns

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
