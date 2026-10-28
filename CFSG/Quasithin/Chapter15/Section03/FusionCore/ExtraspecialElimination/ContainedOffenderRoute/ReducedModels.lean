module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.ClassifiedSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Parabolic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.FieldPreparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.FieldExclusion
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.LateClassification
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection

/-!
# Model reduction for the contained-offender route

`Input` keeps the published placed offender, the separately supplied outside
component, minimality, and the actual ambient Sylow subgroup. From these we
derive the replacement and universal (j), solvability of Y₀T, the intrinsic
cubic quotient, and the component premise for B.5.5 on the genuine actor.

After containment (k), the universal 1.2.1(3) implication collapses the
component orbit, giving H = LT and normality relative to H. Once larger
fields are excluded, the universal component-section implication of
B.5.5/B.4.2 gives every binary group alternative. We then identify the
literal T*-invariant index-three subgroup with the appropriate flag, polar,
or root parabolic. The exceptional hexacode action is retained.

Containment (k) is now proved by `Input.y_le_closure`. Together with the
orbit theorem it gives `structure_of_earlier`, including H = LT and relative
component normality. `parabolic_of_earlier` gives the actual Sylow, index-three,
minimality, invariance and solvability assertions without any field premise.
The full corrected B.5.1 conclusion is supplied on the late actor by
`late_source_conclusion`, with every application hypothesis discharged.

`natural_component_section` now selects the natural action from that full
conclusion. The actual contained offender excludes the S₅ row via its local
two-core, and `no_larger_field_of_earlier` constructs the field exclusion,
including containment, compatible Borel marking and B.2.14 decomposition.
`reduction_of_earlier` completes the conditional (k)–(l) assembly: it supplies
that field exclusion to `reduction_of_field_exclusion`, retaining the actual
component sections, all model equivalences and the geometric parabolics.
`parabolic_of_earlier` also exposes the literal Sylow subgroup, index three,
minimality and solvability for subsequent model exclusions. Existing
conditional interfaces are preserved.

The inputs and their source provenance are as follows.

* `Input.placed` is the published local input: the extraspecial case and
  residual of 15.3.7(2), the theta identity 15.3.49(b), the seed normalizer
  from 15.3.46(5), the literal U_H/Z action from 15.3.48, and the contained
  quadratic best offender placed in O₂(Y₀*T*) after 15.3.49(h). Its SQTK
  premise is inherited from the source local group.
* `Input.component` is the separately supplied outside component with its
  actual inclusion and commutator identity. `Input.minimal` and the original
  ambient Sylow subgroup prove the replacement and universal (j). Constructing
  this component remains with the parent; it is not a classification premise.
* `sections` is the universal B.5.5(1)(iii)–(iv)/B.4.2 component-section
  implication, applied to the genuine first offender-generated actor.
* `orbits` is the universal A.3.8 orbit implication used by 1.2.1(3), applied
  to the actual two-core quotient. It supplies both the orbit bound and models.
* `source` is the full six-clause B.5.1 implication, with the corrected
  projective-line convention in B.4.2(8), applied to the genuine late actor.
* `hB214` is the universal B.2.14 splitting implication. Its characteristic-two
  hypothesis for H/Z is proved from the action. The only additional local
  premises, `hZST` and `h48`, are Z_S ≤ T and [Z_S,T] ≤ Z from 15.3.48(2).

The parent must discharge these universal earlier implications and the
published local inputs before claiming the full 15.3.49. The A.3.18 exceptional
exclusions and the intrinsic Borel/field calculations are already proved by
the containment development; no extra implication for them is assumed here.
No solvability of M ∩ H or component generation of the first actor is used,
and no bound |Y₀*| = 3 is imposed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(k)–(l), printed pp.1143–1145; B.5.5, pp.104–105; 1.2.1(3), p.504.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open Subgroup ComponentReduction ModelReduction BinaryModels ModelSieve
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative

universe u v

/-- The geometric alternatives in (l), as outputs. Each Lie-type branch
identifies the actual subgroup P under an actual component equivalence.
The exceptional branches assert precisely the source's exceptions. -/
inductive ParabolicAlternative {D : Type u} [Group D] {W : Type v}
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C P : Subgroup D) : Prop
  | linear (n : ℕ) [NeZero n] (lo : 3 ≤ n) (hi : n ≤ 5)
      (position : ModelExclusions.BinaryGeometry.Position C P n)
  | six (e : C ≃* Theory.SpecificGroups.SymmetricSix.A6)
      (g : Theory.SpecificGroups.SymmetricSix.A6) (i : Bool)
      (position : (P.subgroupOf C).map
          (e.trans ParabolicIdentification.Six.alternatingEquivDerived).toMonoidHom =
        ((Theory.SpecificGroups.SymplecticFour.stabilizer
          (ParabolicIdentification.Six.markedSpace i)).map
            (MulAut.conj (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
              g.val)).toMonoidHom).subgroupOf
                (commutator (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2))))
  | g2 (e : C ≃* Atlas.G2.BinaryParabolicPair.DerivedModel)
      (g : Atlas.G2.Model (ZMod 2)) (i : Fin 2)
      (position : (P.subgroupOf C).map e.toMonoidHom =
        ((if i = 0 then Atlas.G2.LieParabolicSetup.parabolic₁ else
          Atlas.G2.LieParabolicSetup.parabolic₂).map
            (MulAut.conj g).toMonoidHom).subgroupOf
              Atlas.G2.BinaryParabolicPair.DerivedModel)
  | seven (model : Nonempty (C ≃* alternatingGroup (Fin 7)))
  | triple_cover (sectionModel : Nonempty (HexSection ρ C))

namespace Input
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- The exact local parabolic properties, now with containment and closure
equality discharged. These feed binary-generation and point-case consumers
without the stronger legacy `BinaryModels.LocalControl` assumptions. -/
theorem parabolic_of_earlier
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ) :
    IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L) ∧
      ModelExclusions.componentParabolic H L Y0 T ≤ starImage H L ∧
      (starImage H (T ⊓ L)).relIndex
        (ModelExclusions.componentParabolic H L Y0 T) = 3 ∧
      starImage H (T ⊓ L) ⋖ ModelExclusions.componentParabolic H L Y0 T ∧
      starImage H T ≤ normalizer
        (ModelExclusions.componentParabolic H L Y0 T : Set (H ⧸ pCore 2 H)) ∧
      Group.IsSolvable (ModelExclusions.componentParabolic H L Y0 T) ∧
      ModelExclusions.ReducedLocalData H M L Y0 T := by
  obtain ⟨he, hy, _, _, _, _, _⟩ := d.structure_of_earlier sections orbits
  obtain ⟨hs, hp, hi, hm, ht⟩ := d.parabolic_local he hy
  exact ⟨hs, hp, hi, hm, ht, d.parabolic_solvable,
    d.reduced_data orbits (d.y_le_closure sections)⟩

/-- Every model branch supplies its actual geometric alternative, using the
same component equivalence. Containment and field exclusion remain premises. -/
theorem parabolic_alternatives (sections : EarlierComponentSections κ)
    (hclosed : localSpan L T = L) (hy : Y0 ≤ L)
    (hfield : NoLargerField (L ⧸ pCore 2 L)) :
    ParabolicAlternative d.placed.action.representation (starImage H L)
      (ModelExclusions.componentParabolic H L Y0 T) := by
  have hs := (d.binary_sections sections hfield).1
  cases hs with
  | linear n lo hi model =>
    let : NeZero n := ⟨by omega⟩
    obtain ⟨e⟩ := model
    obtain ⟨pos, _⟩ := d.linear_position hclosed hy n lo hi e
    exact .linear n lo hi pos
  | alternating_six model =>
    obtain ⟨e⟩ := model
    obtain ⟨g, i, hp⟩ := d.six_position hclosed hy e
    exact .six e g i hp
  | g2_derived model =>
    obtain ⟨e⟩ := model
    obtain ⟨g, i, hp⟩ := d.g2_position hclosed hy e
    exact .g2 e g i hp
  | alternating_seven model => exact .seven model
  | triple_cover sectionModel => exact .triple_cover sectionModel

/-- Final algebraic and geometric assembly after the two missing local
deductions. This is deliberately named for its remaining premises, not as
a proof of source (k) or of the larger-field exclusion. -/
theorem reduction_of_containment_and_field_exclusion
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (sections : EarlierComponentSections κ)
    (hcontainment : Y0 ≤ localSpan L T)
    (hfield : NoLargerField (L ⧸ pCore 2 L)) :
    localSpan L T = L ∧ Y0 ≤ L ∧ H = L ⊔ T ∧
      (L.subgroupOf H).Normal ∧ H ≤ normalizer (L : Set G) ∧
      BinarySectionAlternative d.placed.action.representation (starImage H L) ∧
      BinaryComponentModel (L ⧸ pCore 2 L) ∧
      starImage H (T ⊓ L) ⋖ ModelExclusions.componentParabolic H L Y0 T ∧
      starImage H T ≤ normalizer
        (ModelExclusions.componentParabolic H L Y0 T : Set (H ⧸ pCore 2 H)) ∧
      ParabolicAlternative d.placed.action.representation (starImage H L)
        (ModelExclusions.componentParabolic H L Y0 T) ∧
      ModelExclusions.ReducedLocalData H M L Y0 T := by
  obtain ⟨he, hy, hg, hn, hnorm, _, _⟩ := d.reduced_structure orbits hcontainment
  obtain ⟨hsections, hmodel, _⟩ := d.binary_sections sections hfield
  obtain ⟨_, _, _, hmin, hinv⟩ := d.parabolic_local he hy
  exact ⟨he, hy, hg, hn, hnorm, hsections, hmodel, hmin, hinv,
    d.parabolic_alternatives sections he hy hfield, d.reduced_data orbits hcontainment⟩

/-- All algebraic and geometric alternatives after the remaining field
exclusion. Unlike the preserved older wrapper, this theorem proves (k)
from the earlier component-section implication. It is still conditional
on the field exclusion, which the final assembly must discharge. -/
theorem reduction_of_field_exclusion
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (sections : EarlierComponentSections κ)
    (hfield : NoLargerField (L ⧸ pCore 2 L)) :
    localSpan L T = L ∧ Y0 ≤ L ∧ H = L ⊔ T ∧
      (L.subgroupOf H).Normal ∧ H ≤ normalizer (L : Set G) ∧
      BinarySectionAlternative d.placed.action.representation (starImage H L) ∧
      BinaryComponentModel (L ⧸ pCore 2 L) ∧
      starImage H (T ⊓ L) ⋖ ModelExclusions.componentParabolic H L Y0 T ∧
      starImage H T ≤ normalizer
        (ModelExclusions.componentParabolic H L Y0 T : Set (H ⧸ pCore 2 H)) ∧
      ParabolicAlternative d.placed.action.representation (starImage H L)
        (ModelExclusions.componentParabolic H L Y0 T) ∧
      ModelExclusions.ReducedLocalData H M L Y0 T :=
  d.reduction_of_containment_and_field_exclusion orbits sections
    (d.y_le_closure sections) hfield

/-- Conditional 15.3.49(k)–(l) with every intermediate local deduction
discharged. The four universal earlier implications are enumerated above;
the two additional seed conditions are precisely from 15.3.48(2).

The component is the separately supplied witness in `d`, and the action
remains its original SectionAction on U_H/Z. Containment, closure equality,
field exclusion and model selection are conclusions of the proof. In
particular the geometric alternative concerns the literal Y₀*(T ∩ L)*,
and the exceptional branch keeps its compatible hexacode section. -/
theorem reduction_of_earlier
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) :
    localSpan L T = L ∧ Y0 ≤ L ∧ H = L ⊔ T ∧
      (L.subgroupOf H).Normal ∧ H ≤ normalizer (L : Set G) ∧
      BinarySectionAlternative d.placed.action.representation (starImage H L) ∧
      BinaryComponentModel (L ⧸ pCore 2 L) ∧
      starImage H (T ⊓ L) ⋖ ModelExclusions.componentParabolic H L Y0 T ∧
      starImage H T ≤ normalizer
        (ModelExclusions.componentParabolic H L Y0 T : Set (H ⧸ pCore 2 H)) ∧
      ParabolicAlternative d.placed.action.representation (starImage H L)
        (ModelExclusions.componentParabolic H L Y0 T) ∧
      ModelExclusions.ReducedLocalData H M L Y0 T :=
  d.reduction_of_field_exclusion orbits sections
    (d.no_larger_field_of_earlier sections orbits source hB214 hZST h48)

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
