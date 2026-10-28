module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitSupplement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenModules
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor

/-!
# The corrected B.5.1 theorem on the actual doubled orbit

The marked doubled seed gives two nonisomorphic simple constituents for the
literal component action on W. Their endomorphism fields have odd unit groups,
so every normal two-subgroup of an offender supplement acts trivially. The
supplement action is faithful, hence its two-core is trivial. This discharges
the missing hypothesis for all six clauses of the corrected B.5.1 theorem.

The original component projection and orbit coordinates are retained throughout.
The implementation imports expose their definitions only to verify the literal
conjugation formula. No irreducibility assumption is made on the whole orbit.
The subsequent row selection and ambient normalizer comparison remain separate.

Source: Aschbacher--Smith, B.5.1, D.3.10, 3.2.5 and 12.2.2, printed
pp.99--103, 201, 580 and 795--796.
-/

public noncomputable section
open scoped IsMulCommutative

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
/-- The original irreducible seed remains irreducible under the literal L-action. -/
theorem doubledSeed_irreducible [IsElementaryAbelian 2 V]
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    IsIrreducible (doubledSeedAction L V D.normalizes) := by
  let σ := (D.seedRepresentation.comp D.componentImage.subtype).comp D.componentHom
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff D.componentHom D.componentHom_surjective _).mpr
      (D.seed_irreducible hc)
  let e : D.space ≃ₗ[ZMod 2] Additive V :=
    (MulEquiv.toAdditiveRight D.spaceEquiv).toLinearEquiv (ZMod.map_smul _)
  let a : σ ≃ₗ doubledSeedAction L V D.normalizes := ⟨e, fun l => by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (D.spaceEquiv (Multiplicative.ofAdd (σ l v)) : G) =
      (l : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹
    rw [D.spaceEquiv_apply, D.spaceEquiv_apply]
    rfl⟩
  exact (RepEquiv.irreducible_euqiv a).mp hi

omit [Finite G] in
/-- The original component projection acts by literal ambient conjugation
on the original orbit coordinates. -/
theorem doubledOrbit_component_action (l : L) (w : D.orbitSpace) :
    D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitComponentHom l) w) =
      doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l
        (D.sourceOrbitCoordinates w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (D.sourceOrbitCoordinates_apply
    (D.orbitRepresentation (D.orbitComponentHom l) w)).trans
      (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹)
        (D.sourceOrbitCoordinates_apply w).symm)

/-- A normal two-subgroup of an offender supplement centralizes the
component, hence both distinct simple summands of the original doubled orbit. -/
theorem doubledOrbit_supplement_twoCore (hd : D.MarkedDoubled)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup (linearNormalizer
      (D.orbitRepresentation.comp D.orbitComponent.subtype))) :
    pCore 2 (supplement (D.orbitRepresentation.comp D.orbitComponent.subtype) A) = ⊥ := by
  let := D.elementary
  let σ := D.orbitRepresentation.comp D.orbitComponent.subtype
  let := D.orbitComponent_quasisimple h
  have hf : Function.Injective σ :=
    (subspaceImageRepresentation_injective _ _).comp D.orbitComponent.subtype_injective
  have hp := @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  rcases hp with ⟨t,ht,hnt,hne,e,heV,he⟩
  let α := doubledSeedAction L V D.normalizes
  let β := α.comp (doubledTwist L t (D.sylow_normalizes_component ht)).toMonoidHom
  let := D.doubledSeed_irreducible hd.1
  let : IsIrreducible β :=
    (irreducible_comp_surjective_iff _ (doubledTwist L t
      (D.sylow_normalizes_component ht)).surjective α).mpr inferInstance
  let c := D.sourceOrbitCoordinates.trans e.symm
  apply ModuleClassification.DoubledOrbit.supplement_twoCore_of_pair σ hf A
    D.orbitComponentHom α β hne c
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

/-- All six corrected B.5.1 clauses apply on the actual doubled orbit.
No irreducibility of that orbit is asserted or assumed. -/
theorem doubledOrbit_normalizer_offender_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (A : Subgroup (linearNormalizer
      (D.orbitRepresentation.comp D.orbitComponent.subtype)))
    (hA : IsOffender D.sourceOrbitNormalizerRepresentation A) :
    ModuleClassification.NormalizerConclusion
      (D.orbitRepresentation.comp D.orbitComponent.subtype) A := by
  let σ := D.orbitRepresentation.comp D.orbitComponent.subtype
  have hf : Function.Injective σ :=
    (subspaceImageRepresentation_injective _ _).comp D.orbitComponent.subtype_injective
  let := D.orbitComponent_quasisimple h
  exact ModuleClassification.DoubledOrbit.normalizer_source_of_twoCore σ hf A
    ((D.sourceOrbit_sqtk h).subgroup D.orbitComponent)
    (D.doubledOrbit_supplement_twoCore hd h A) hA

/-- The supplied full-linear-normalizer FF witness is classified on W itself. -/
theorem doubledOrbit_full_normalizer_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hff : IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ A : Subgroup (linearNormalizer
      (D.orbitRepresentation.comp D.orbitComponent.subtype)),
      IsOffender D.sourceOrbitNormalizerRepresentation A ∧
      ModuleClassification.NormalizerConclusion
        (D.orbitRepresentation.comp D.orbitComponent.subtype) A := by
  obtain ⟨A,hA⟩ := hff
  exact ⟨A,hA,D.doubledOrbit_normalizer_offender_source h hd A hA⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
