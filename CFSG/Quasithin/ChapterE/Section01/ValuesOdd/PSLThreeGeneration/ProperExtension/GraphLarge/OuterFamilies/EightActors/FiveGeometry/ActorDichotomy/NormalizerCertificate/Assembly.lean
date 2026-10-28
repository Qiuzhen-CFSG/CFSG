module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.NormalizerCertificate.WeakClosure

/-!
# Monomial and weak-closure normalizer generation in PSL₃(5):2

The fixed coordinate Sylow lies in the literal split monomial overgroup. The
family census identifies its weak closure with the join of the original actor
and its specified conjugate, so both explicit block matrices normalize that
weak closure. Their elementary-matrix generation certificate then proves that
the monomial overgroup and this normalizer generate the whole graph extension.

This discharges `MonomialJoin` without additional premises. Its application to
`solvable_join_at_every_sylow` supplies a solvable generating overgroup for the
same conjugacy family at every Sylow. The other actor orbit and the residual
quotient alternative belong to the separate reselection argument.

Source: Aschbacher--Smith E.1.5 and the PSL₃(5):2 calculation supporting
E.1.14(7), printed pp.210 and 214. The literal carrier and matrix generation
retain their imported ATLAS attribution and `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.NormalizerCertificate
open FiveSourceAudit OuterReselection

/-- The first displayed block matrix normalizes the original family's exact
weak closure in the fixed Sylow. -/
theorem first_normalizes_weakClosure :
    innerSL firstMatrix ∈ normalizer
      (weakClosure (standardSylow : Subgroup Model) family : Set Model) := by
  rw [WeakClosure.weakClosure_standardSylow]
  exact first_normalizes_actorJoin

/-- The second displayed block matrix normalizes that same weak closure. -/
theorem second_normalizes_weakClosure :
    innerSL secondMatrix ∈ normalizer
      (weakClosure (standardSylow : Subgroup Model) family : Set Model) := by
  rw [WeakClosure.weakClosure_standardSylow]
  exact second_normalizes_actorJoin

/-- The literal monomial overgroup and the actual family weak-closure
normalizer generate the full automorphism carrier. -/
theorem monomial_sup_weakClosure_normalizer :
    monomialOvergroup ⊔ normalizer
      (weakClosure (standardSylow : Subgroup Model) family : Set Model) = ⊤ :=
  eq_top_of_monomial_and_matrices _ le_sup_left
    (mem_sup_right first_normalizes_weakClosure)
    (mem_sup_right second_normalizes_weakClosure)

/-- The first-orbit calculation required by the actor-dichotomy consumer,
with the Sylow placement and complete weak-closure calculation discharged. -/
theorem monomialJoin : MonomialJoin :=
  ⟨standardSylow, WeakClosure.standardSylow_le_monomialOvergroup,
    monomial_sup_weakClosure_normalizer⟩

/-- At every actual Sylow, the original conjugacy family's weak-closure
normalizer generates with a solvable overgroup containing that Sylow. -/
theorem solvable_overgroup_at_every_sylow (T : Sylow 2 Model) :
    ∃ H : Subgroup Model, (T : Subgroup Model) ≤ H ∧ Group.IsSolvable H ∧
      H ⊔ normalizer (weakClosure (T : Subgroup Model) family : Set Model) = ⊤ :=
  solvable_join_at_every_sylow monomialJoin T

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.NormalizerCertificate
