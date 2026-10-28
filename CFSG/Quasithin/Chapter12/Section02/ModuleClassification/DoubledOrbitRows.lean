module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitOffenders
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitHomogeneity
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor
/-!
# The natural-plus-dual row on the original doubled orbit

B.5.1 is applied to the actual offender subgroup of a linear-normalizer
supplement. Its component is identified with the original faithful action
image by the original projection. Pulling back through L retains both
nonisomorphic irreducible summands, so DoubledOrbitHomogeneity excludes the
homogeneous alternative and selects degree four or five.

The last theorem discharges the source-classification premise using the
retained doubledOrbit_full_normalizer_source. No ambient H.9 model or
irreducibility of the whole doubled space is assumed. The implementation
imports retain the canonical orbit constructions used in this transport.
DoubledOrbitCover recovers the literal L/O₂(L) marking from this action.

Source: Aschbacher--Smith, B.5.1(3), D.3.10 and 12.2.2, printed
pp.99, 201 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
open Representation.BinaryOffender.QuasisimpleNormalizer
universe u
variable {P W : Type u} {J U Z : Type*} [Group P] [Group J]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal component in the offender subgroup is the same faithful
component as the one acting on the original space. -/
theorem naturalDual_of_normalizer_pair
    (σ : Representation (ZMod 2) P W) (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) (hA : NormalizerConclusion σ A)
    (q : J →* P) (hq : Function.Surjective q)
    (α : Representation (ZMod 2) J U) (β : Representation (ZMod 2) J Z)
    [IsIrreducible α] [IsIrreducible β]
    (hne : ¬ Nonempty (α.Equiv β)) (hz : σ.invariants = ⊥)
    (e : W ≃ₗ[ZMod 2] (U × Z))
    (he : ∀ g w, e (σ (q g) w) = (α.prod β) g (e w)) :
    ∃ n, (n = 4 ∨ n = 5) ∧ IsNaturalPlusDual σ n := by
  let C := component σ A
  let I := offenderSubgroup (linearAction (supplement σ A))
  let K := C.subgroupOf I
  let ρ := (linearAction (supplement σ A)).comp I.subtype
  let p : P →* K :=
    ((subgroupOfEquivOfLe hA.1).symm.toMonoidHom).comp (projection σ A)
  have hp : Function.Surjective p :=
    (subgroupOfEquivOfLe hA.1).symm.surjective.comp (projection_surjective σ A)
  have hpi : Function.Injective p := by
    intro x y hxy
    apply hf
    exact congrArg (fun k : K => ρ k) hxy
  let ep : P ≃* K := MulEquiv.ofBijective p ⟨hpi,hp⟩
  have hfix : fixedSpace ρ K = ⊥ := by
    apply bot_unique
    intro w hw
    apply hz.le
    intro g
    exact hw (p g)
  obtain ⟨c⟩ := hA.2
  obtain ⟨n,hn,⟨a⟩⟩ := naturalDual_of_source_pair ρ K c (p.comp q) (hp.comp hq)
    α β hne hfix e he
  exact ⟨n,hn,⟨⟨ep.trans a.groupEquiv,a.linearEquiv,
    fun g w => a.intertwines (p g) w⟩⟩⟩
end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
/-- The component action is its literal faithful action image. -/
theorem doubledOrbit_component_faithful :
    Function.Injective (D.orbitRepresentation.comp D.orbitComponent.subtype) := by
  intro x y hxy
  apply Subtype.ext
  exact subspaceImageRepresentation_injective
    (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace hxy

/-- The genuine B.5.1 conclusion on an offender supplement selects the
natural-plus-dual action on the same original orbit component. -/
theorem doubledOrbit_naturalPlusDual_of_conclusion (hd : D.MarkedDoubled)
    (A : Subgroup (linearNormalizer
      (D.orbitRepresentation.comp D.orbitComponent.subtype)))
    (hA : ModuleClassification.NormalizerConclusion
      (D.orbitRepresentation.comp D.orbitComponent.subtype) A) :
    ∃ n, (n = 4 ∨ n = 5) ∧
      IsNaturalPlusDual (D.orbitRepresentation.comp D.orbitComponent.subtype) n := by
  let σ := D.orbitRepresentation.comp D.orbitComponent.subtype
  have hf : Function.Injective σ := D.doubledOrbit_component_faithful
  have hz := D.orbit_fixedSpace_eq_bot hd.1
  let := D.elementary
  have hp := @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  rcases hp with ⟨t,ht,_,hne,e,_,he⟩
  let α := doubledSeedAction L V D.normalizes
  let β := α.comp (doubledTwist L t (D.sylow_normalizes_component ht)).toMonoidHom
  let : IsIrreducible α := D.doubledSeed_irreducible hd.1
  let : IsIrreducible β :=
    (irreducible_comp_surjective_iff _ (doubledTwist L t
      (D.sylow_normalizes_component ht)).surjective α).mpr inferInstance
  let c := D.sourceOrbitCoordinates.trans e.symm
  apply ModuleClassification.DoubledOrbit.naturalDual_of_normalizer_pair σ hf A hA
    D.orbitComponentHom D.orbitComponentHom_surjective α β hne hz c
  intro l w
  apply e.injective
  calc
    e (c (σ (D.orbitComponentHom l) w)) =
        D.sourceOrbitCoordinates (σ (D.orbitComponentHom l) w) :=
      e.apply_symm_apply _
    _ = doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l
        (D.sourceOrbitCoordinates w) := D.doubledOrbit_component_action l w
    _ = doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l
        (e (c w)) := congrArg
      (doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l)
      (e.apply_symm_apply (D.sourceOrbitCoordinates w)).symm
    _ = e ((α.prod β) l (c w)) := (he l (c w)).symm
/-- The FF doubled orbit is the binary natural-plus-dual row, retaining the
original faithful component action on the whole original orbit space. -/
theorem doubledOrbit_naturalPlusDual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hff : IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ n, (n = 4 ∨ n = 5) ∧
      IsNaturalPlusDual (D.orbitRepresentation.comp D.orbitComponent.subtype) n := by
  obtain ⟨A,_,hA⟩ := D.doubledOrbit_full_normalizer_source h hd hff
  exact D.doubledOrbit_naturalPlusDual_of_conclusion hd A hA
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
