module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo.PolarComparison

/-!
# The binary symplectic endpoint in the nonsplitting list

The concrete polar isomorphism S₆ ≃ Sp₄(2) and the explicit linear map
from the deleted six-letter quotient give an equivalence of the full natural
actions. Restricting that same isomorphism to commutators identifies the
natural action of Sp₄(2)' with the actual A₆ deleted permutation action.

For a marked Sp₄(2) alternative, compose the literal restricted action
from `markedRestriction` with this identification. The resulting A₆ marking
is the original subgroup equivalence followed by the inverse polar map;
no independent choice of a group isomorphism is made in the consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2(3)
and B.5.1(2),(5), printed pp.86,99,102–103. Final assembly of the nonsplitting
and supplement lists remains in `IrreducibleCohomology`.
-/

@[expose] public section

open Representation
open Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.SymplecticTwo

/-- The full natural Sp₄(2)-action is the actual six-letter deleted quotient action. -/
noncomputable def naturalActionEquiv :
    ActionEquiv (symplecticNatural (k := ZMod 2) 2)
      (BinaryPermutation.naturalRepresentation (Fin 6)) :=
  actionSymm
    { groupEquiv := symmetricSymplecticEquiv
      linearEquiv := naturalLinearEquiv
      intertwines := naturalLinearEquiv_equivariant }

/-- The same polar identification, restricted to the actual derived subgroup. -/
noncomputable def derivedNaturalActionEquiv :
    ActionEquiv (symplecticDerivedNatural (k := ZMod 2) 2) (alternatingNatural 6) :=
  actionSymm
    { groupEquiv := alternatingDerivedEquiv
      linearEquiv := naturalLinearEquiv
      intertwines := fun g v => naturalLinearEquiv_equivariant g.val v }

/-- The binary derived symplectic endpoint has the required concrete A₆ natural model. -/
theorem derivedNatural_isAlternatingNatural :
    Nonempty (ActionEquiv (symplecticDerivedNatural (k := ZMod 2) 2)
      (alternatingNatural 6)) :=
  ⟨derivedNaturalActionEquiv⟩

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {H L : Subgroup G}

/-- Transport the marked restriction using precisely its given subgroup identification. -/
noncomputable def markedAlternatingActionEquiv
    (e : MarkedActionEquiv ρ H L (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) :
    ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6) where
  groupEquiv := e.subgroupEquiv.trans derivedNaturalActionEquiv.groupEquiv
  linearEquiv := e.action.linearEquiv.trans derivedNaturalActionEquiv.linearEquiv
  intertwines g v :=
    (congrArg derivedNaturalActionEquiv.linearEquiv ((markedRestriction e).intertwines g v)).trans
      (derivedNaturalActionEquiv.intertwines (e.subgroupEquiv g) (e.action.linearEquiv v))

/-- Explicit compatibility with the original marking of L inside the symplectic model. -/
theorem markedAlternatingActionEquiv_groupEquiv
    (e : MarkedActionEquiv ρ H L (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) :
    (markedAlternatingActionEquiv e).groupEquiv =
      e.subgroupEquiv.trans alternatingDerivedEquiv.symm := rfl

/-- The actual marked B.4.2 binary symplectic case supplies the A₆ row of B.5.1. -/
theorem marked_isAlternatingNatural
    (e : MarkedActionEquiv ρ H L (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) :
    IsAlternatingNatural (ρ.comp L.subtype) 6 :=
  ⟨markedAlternatingActionEquiv e⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.SymplecticTwo
