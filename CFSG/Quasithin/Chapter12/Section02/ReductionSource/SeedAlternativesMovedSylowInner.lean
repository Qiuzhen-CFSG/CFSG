module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowStability
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveInner
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowStability

/-!
# The common cubic actor lies in the actual chosen component

The original nested-image equivalence identifies the restricted component
with `D.componentImage`. In either exceptional B.4.2 row, the common cubic
actor is best on each constituent and its seed image lies in that component.
The pointwise-kernel argument lifts this to the original local-orbit actor.

This supplies the common component actor for the exceptional-model exclusions
in `SeedAlternativesMovedSylowExterior`. Source: Aschbacher--Smith D.3.5(5),
printed pp.195--196. The internal import checks the existing equivalence's
literal subgroup map without changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
theorem orbitSeedActionEquiv_component (D : ChosenModule T L V) :
    (restrictedSubgroup D.orbitRepresentation D.orbitSeed D.orbitComponent).map
      D.orbitSeedActionEquiv.groupEquiv.toMonoidHom = D.componentImage :=
  nestedImageActionEquiv_restricted (reducedRepresentation (L ⊔ (T : Subgroup G)))
    D.orbitSpace D.space (orbitSpan_invariant _ ⊤ D.space) D.seed_le_orbitSpace
    (L.subgroupOf (L ⊔ (T : Subgroup G))) D.irrPlus.invariant

/-- A cubic actor of ratio at most two in either exceptional row lies in the
original component of the faithful local orbit. -/
theorem cubic_le_component_of_exceptional (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hex : D.SeedSieveExceptions)
    (A : Subgroup D.orbitActor) (hA : IsElementaryTwo A)
    (hcu : IsCubic D.orbitRepresentation A)
    (hb : fixedCodim D.orbitRepresentation A ≤ 2 * rank A) : A ≤ D.orbitComponent := by
  let := D.orbitComponent_quasisimple h
  exact le_component_of_marked_image D.orbitRepresentation D.orbitComponent
    (D.orbit_fitting h) D.orbitSeed D.orbitSeed_isIrrPlus.choose
    (D.orbitSeed_isIrrPlus.not_le_fixedSpace D.orbitRepresentation)
    D.orbitSeedActionEquiv.groupEquiv D.componentImage D.orbitSeedActionEquiv_component
    A (D.cubic_stabilizes_seed_of_exceptional h hc hex A hA hcu hb)
    (D.cubic_seed_best_le_component_of_exceptional h hc hm hex A hA hcu hb).2.1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
