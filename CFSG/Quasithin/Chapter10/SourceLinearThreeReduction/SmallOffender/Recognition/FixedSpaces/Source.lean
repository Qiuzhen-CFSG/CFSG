module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.IntersectionsContract
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.FixedVectors
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.DisplacementZero
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Fusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Source

/-!
# Assembly of the uniform large-offender fixed-space argument

The size bound supplies a nonfixed normalizing involution at every corank-two
intersection. Vanishing of its displacement makes the whole offender fix its
fixed space. The proved component-action argument supplies a vector in that space
not fixed by L, so the two-factor permutation forces offender normalization.
The intersection argument then works for every nonfixed offender element.

The centralizing-Thompson branch is proved directly by fusion.
This is a conditional assembly of `GeometryAt`, with the remaining intersection
and residual obligation explicitly retained; the component-action obligation
is discharged by `FixedVectors.source_actionsAt`. It does not claim those
source obligations, or unconditional recognition. The final theorem applies
the result to the actual recognition consumer, independently of model bounds.
Source: Aschbacher--Smith 10.2.12 through (*), printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The complete uniform argument with its precise earlier source inputs. -/
theorem fixedSpaceGeometry_of_source_inputs
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (inputs : ActionInputs D) (intersections : IntersectionInputs D) :
    FixedSpaceGeometry D := by
  intro x hx hsmall
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj x).toMonoidHom
  let A := P ⊓ D.maximalLocal
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  obtain ⟨b,hb,hbM,hbN,hbn⟩ := exists_nonfixed_normalizing_element D c.nonnormal c.size hsmall
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b (show b ∈ P from hb)
  have hzero := displacement_eq_bot D c inputs intersections hx ht htn
    (b := b) ⟨⟨hb,hbM⟩,hbN⟩ hbn
  have hfix : W ⊓ centralizer ({b} : Set G) ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hAN : A ≤ normalizer (W : Set G) :=
    source_nonnormal_normalizes_moved_of_fixed_subgroup D c.nonnormal ht htn
      (c.crossed t ht htn) (W ⊓ centralizer ({b} : Set G)) A inf_le_left
      (inputs.nonfixed b hbM hbN hb2) inf_le_right hfix
  refine ⟨hAN,?_⟩
  intro a ha han
  have hfixed := normalizer_fixed_space c (intersections.outside x hx) ha.1 han
  change W ⊓ centralizer ({a} : Set G) ≤
    centralizer ((A ⊓ normalizer (W : Set G) : Subgroup G) : Set G) at hfixed
  simpa only [inf_of_le_left hAN] using hfixed

/-- Assembly from the two input packets; the action packet is discharged below. -/
theorem geometryAt_of_source_inputs (hi : IntersectionsAt T) (ha : ActionsAt T) :
    GeometryAt T := by
  intro hmany L D hminimal hn hnotA5 hcent hcross hsize
  let c : Context D := ⟨hmany,hminimal,hn,hnotA5,hcent,hcross,hsize⟩
  by_cases hf : FusionCase D
  · exact fixedSpaceGeometry_of_fusion D c hf (involution_fixed_not_le D c)
  · exact fixedSpaceGeometry_of_source_inputs D c (actionInputs_of_nonfixed D c (ha L D c hf))
      ((hi L D c).resolve_left hf)

/-- Actual application to the published recognition consumer. Model bounds
remain independent; neither producer is silently supplied by this theorem. -/
theorem recognition_of_models_and_source_inputs (hmodels : ModelBoundsAt T)
    (hi : IntersectionsAt T) (ha : ActionsAt T) : RecognitionAt T :=
  recognition_of_model_bounds_and_geometry hmodels (geometryAt_of_source_inputs hi ha)

/-- Only the earlier intersection/residual source branch remains outstanding. -/
theorem geometryAt_of_intersections (hi : IntersectionsAt T) : GeometryAt T :=
  geometryAt_of_source_inputs hi source_actionsAt

/-- The actual recognition consumer with the action premise discharged. -/
theorem recognition_of_models_and_intersections (hmodels : ModelBoundsAt T)
    (hi : IntersectionsAt T) : RecognitionAt T :=
  recognition_of_model_bounds_and_geometry hmodels (geometryAt_of_intersections hi)

/-- Assembly from the independent 10.2.6 and 10.2.10 source producers. -/
theorem geometryAt_of_halfSylowUnique_and_intersections
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hi : IntersectionsOfNormalizersAt T) : GeometryAt T :=
  geometryAt_of_intersections (intersectionsAt_of_halfSylowUnique hhalf hi)

/-- The parent's literal recognition application with all action inputs proved. -/
theorem recognition_of_models_halfSylowUnique_and_intersections
    (hmodels : ModelBoundsAt T) (hhalf : PointControl.HalfSylowUniqueAt T)
    (hi : IntersectionsOfNormalizersAt T) : RecognitionAt T :=
  recognition_of_model_bounds_and_geometry hmodels
    (geometryAt_of_halfSylowUnique_and_intersections hhalf hi)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
