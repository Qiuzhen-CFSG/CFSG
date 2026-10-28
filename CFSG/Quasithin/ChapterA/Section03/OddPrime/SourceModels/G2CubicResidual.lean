module
public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.SpecificGroups.G2.CubicFieldActors
public import Theory.GroupAction.ComponentRankAction.ResidualSource

/-!
# The full cubic G₂ residual

Two commuting constant rank-one cubic elements give an elementary nine
in every characteristic-two G₂ model. They remain in every pure
field fixed subgroup, so a nontrivial cubic field actor would force rank
three in the actual component action. The ambient SQTK rank bound excludes
it. The original component is therefore the prime-to-three residual,
including nonsplit cubic tori and central two-covers.

Source: Aschbacher--Smith A.3.18, used in 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual
variable {G : Type*} [Group G] [Finite G]

/-- The exact component and its marked center quotient determine both cubic closures. -/
theorem component_eq_primeClosure_and_residual
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : IsComponent G L) (hZ : IsPGroup 2 (center L))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (L ⧸ center L) ≃* Atlas.G2.Model F) :
    L = closure {x : G | orderOf x = 3} ∧ L = primeToResidual 3 G := by
  let := hL.2
  have hz : Nat.Coprime 3 (Nat.card (center L)) := by
    obtain ⟨m,hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hr : 2 ≤ primeRank 3 L := by
    have hh := Atlas.G2.CubicFieldActors.cubic_rank (F := F)
    rw [←primeRank_congr 3 e] at hh
    exact hh.trans (primeRank_quotient_le_of_coprime 3 (center L) hz)
  have hb := hG.stronglyQuasithin 3 Nat.prime_three (by decide)
  apply Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual hL hz hr hb e
  intro a ha m hm
  exact Atlas.G2.CubicFieldActors.cubic_primePower_actor_inner hF (action L e).range
    (inner_le_range L e) (range_rank_le_two L e hz hr hb) a ha ⟨m,hm⟩

/-- A marked two-core quotient recovers the central kernel without assuming L centerless. -/
theorem component_eq_cubic_residual_of_twoCore_model
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : IsComponent G L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model F) :
    L = primeToResidual 3 G := by
  let := hL.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hz : center L = pCore 2 L := by
    apply le_antisymm _ (IsQuasisimple.pCore_le_center 2)
    intro x hx
    have hc : f x ∈ center (Atlas.G2.Model F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y,rfl⟩ := hf y
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)
    rw [Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hF,mem_bot] at hc
    apply (QuotientGroup.eq_one_iff x).mp
    exact e.map_eq_one_iff.mp hc
  have hZ : IsPGroup 2 (center L) := hz.symm ▸ pCore_isPGroup
  let d : (L ⧸ center L) ≃* Atlas.G2.Model F :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans e
  exact (component_eq_primeClosure_and_residual hG hL hZ hF d).2

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual
