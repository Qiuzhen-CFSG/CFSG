module
public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.SpecificGroups.ReeF4.CubicFieldActors
public import Theory.GroupAction.ComponentRankAction.ResidualSource

/-!
# The cubic Ree residual

The prime-field elementary nine is fixed by every field actor. A nontrivial
cubic field actor would therefore force three-rank at least three in the
actual component action, contradicting SQTK. Simplicity and perfectness
of the native carrier are inherited from the actual central quotient.

Source: Aschbacher--Smith A.3.18 and 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual
variable {G : Type*} [Group G] [Finite G]

/-- The exact component and its marked center quotient determine both cubic closures. -/
theorem component_eq_primeClosure_and_residual
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : IsComponent G L) (hZ : IsPGroup 2 (center L))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ center L) ≃* ReeF4.Model m) :
    L = closure {x : G | orderOf x = 3} ∧ L = primeToResidual 3 G := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hz : Nat.Coprime 3 (Nat.card (center L)) := by
    obtain ⟨m,hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hr : 2 ≤ primeRank 3 L := by
    have hh := ReeF4.CubicRank.model m
    rw [←primeRank_congr 3 e] at hh
    exact hh.trans (primeRank_quotient_le_of_coprime 3 (center L) hz)
  have hb := hG.stronglyQuasithin 3 Nat.prime_three (by decide)
  apply Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual hL hz hr hb e
  intro a ha k hk
  exact ReeF4.CubicFieldActors.cubic_primePower_actor_inner hm (action L e).range
    (inner_le_range L e) (range_rank_le_two L e hz hr hb) a ha ⟨k,hk⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual
