module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.Seed
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.Original

/-!
# The original F.9.18 input to the D.3 module analysis

The literal quotient H/O₂(H) inherits SQTK, its component orbit is normal,
and its action on U_H/V₁ is faithful. A homogeneous Irr⁺ seed exists in
that module. The two-core invariance proved in `Seed` establishes every
internal module hypothesis of D.3.2. Applying D.3.3 then gives the faithful
image of the actual full orbit, with its precise Sylow and component images.

The same selected seed and the same edge actor satisfy F.9.18(2--3),
including the faithful quadratic actions and both ratio bounds on each
intermediate span. Relative normality of K in H is equivalent to the
single-component branch in H/O₂(H). It is not imposed on the general
construction, and it remains for the component assembly owner to prove.

These are input reductions, not the model classification in F.9.18(4--5).
The D.3 orbit alternatives and the unmarked B.4 small-ratio classification
are still needed to obtain `Models.F918Models` and discharge
`CoverModels.original_catalogue_or_suzuki`. Final assembly remains with
qt-d-138-f918-models-source; qt-d-138-components-source owns the relative
normality and Suzuki exclusions. All earlier source premises are retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.18, printed pp.325--326; D.3.1--4, pp.193--194;
and original 13.8.15--17, pp.952--953.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open CriticalGeometry.Reorientation
open SourceCompletion SolvableExclusion Three Three.Supercritical.Offenders
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Swapped.LinearTwo.ModuleAlternatives.F918Sections
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The image of the original Sylow subgroup through H → H/O₂(H). -/
noncomputable def starSylow (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) : Sylow 2 (Source.Hstar H) :=
  (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))

@[simp] theorem starSylow_coe (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) :
    (starSylow H T hTH : Subgroup (Source.Hstar H)) = Source.starImage H T := rfl

private theorem star_orbit_eq (H K : Subgroup G) (T : Sylow 2 G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H) :
    Source.starImage H (conjugateSpanBy K (T : Subgroup G)) =
      componentOrbit (Source.starImage H K) (starSylow H T hTH) := by
  rw [starSylow_coe, star_conjugateSpan H K T hKH hTH,
    conjugateSpanBy_eq_iSup_conj]
  rfl

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)

include d h hF9all hcentral hcomm hsource hH hKH hK

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The earlier source component argument normalizes the entire orbit. -/
theorem source_orbit_normal :
    (componentOrbit (Source.starImage H K)
      (starSylow H T (le_sup_right.trans hH.1.2))).Normal := by
  have hn := (LocalFitting.source_component d hH hsource
    (SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource)
    K hKH hK).2.2.1
  have hOH : conjugateSpanBy K (T : Subgroup G) ≤ H :=
    conjugateSpanBy_le hKH ((le_sup_right.trans hH.1.2).trans H.le_normalizer)
  let : ((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOH).mpr hn
  rw [← star_orbit_eq H K T hKH (le_sup_right.trans hH.1.2)]
  exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective (pCore 2 H))

/-- Every homogeneous source seed satisfies the internal D.3 module hypotheses. -/
theorem source_internal_module
    (a : Five.StarAction H (Source.UH H V₃) V₁)
    {I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁))}
    (hI : IsIrrPlusWith (linearAction a)
      (componentOrbit (Source.starImage H K) (starSylow H T (le_sup_right.trans hH.1.2)))
      (starSylow H T (le_sup_right.trans hH.1.2)) I) :
    ChapterD.Section03.InternalModuleHypotheses KnownSimple.IsKnownSimple
      (linearAction a) (starSylow H T (le_sup_right.trans hH.1.2))
      (componentOrbit (Source.starImage H K) (starSylow H T (le_sup_right.trans hH.1.2))) I := by
  have hf := linearAction_injective a (a.injective_of_kernel (OddReduction.source_kernel (hF9all H hH)))
  have hq := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  exact internal_module_of_component_orbit (linearAction a)
    (CoverModels.original_star_sqtk d hH) hf (pCore_quotient_pCore_eq_bot 2)
    (Source.starImage H K) (starSylow H T (le_sup_right.trans hH.1.2))
    (star_isComponent H K hK hq)
    (source_orbit_normal d h hF9all hcentral hcomm hsource hH K hKH hK) hI

omit hKH in
/-- Select a homogeneous seed without a classification or chosen-module premise. -/
theorem source_homogeneous_seed (a : Five.StarAction H (Source.UH H V₃) V₁) :
    ∃ I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)),
      IsIrrPlusWith (linearAction a)
        (componentOrbit (Source.starImage H K) (starSylow H T (le_sup_right.trans hH.1.2)))
        (starSylow H T (le_sup_right.trans hH.1.2)) I := by
  have hf := linearAction_injective a (a.injective_of_kernel (OddReduction.source_kernel (hF9all H hH)))
  have hq := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  have hc := star_isComponent H K hK hq
  let S := starSylow H T (le_sup_right.trans hH.1.2)
  let X := componentOrbit (Source.starImage H K) S
  let : Group.IsPerfect X := hc.orbit_isPerfect S
  have hX : X ≠ ⊥ := by
    intro he
    exact hc.isCComponent.ne_bot (bot_unique (he ▸ le_componentOrbit (Source.starImage H K) S))
  exact exists_isIrrPlusWith_of_faithful (linearAction a) hf X S hX
    (le_normalizer_componentOrbit _ _) S.isPGroup'

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- Relative normality is exactly the single-component branch on H/O₂(H). -/
theorem source_orbit_eq_iff_normal :
    componentOrbit (Source.starImage H K)
      (starSylow H T (le_sup_right.trans hH.1.2)) = Source.starImage H K ↔
      (K.subgroupOf H).Normal := by
  constructor
  · intro he
    have hn := source_orbit_normal d h hF9all hcentral hcomm hsource hH K hKH hK
    rw [he] at hn
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    exact cComponent_normal_of_quotient_normal hK (pCore 2 H) hn
  · intro hn
    rw [← star_orbit_eq H K T hKH (le_sup_right.trans hH.1.2),
      conjugateSpan_eq_of_normal H K T hKH (le_sup_right.trans hH.1.2) hn]

/-- Apply D.3.3 to the actual full orbit of a homogeneous source seed. -/
theorem source_faithful_orbit
    (a : Five.StarAction H (Source.UH H V₃) V₁)
    {I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁))}
    (hI : IsIrrPlusWith (linearAction a)
      (componentOrbit (Source.starImage H K) (starSylow H T (le_sup_right.trans hH.1.2)))
      (starSylow H T (le_sup_right.trans hH.1.2)) I) :
    let ρ := linearAction a
    let S := starSylow H T (le_sup_right.trans hH.1.2)
    let X := componentOrbit (Source.starImage H K) S
    let W := orbitSpan ρ ⊤ I
    ChapterD.Section03.SourceHypotheses KnownSimple.IsKnownSimple
      (subspaceImageRepresentation ρ W)
      (S.mapSurjective (invariantActionHom_surjective ρ W (orbitSpan_invariant ρ ⊤ I)))
      (restrictedSubgroup ρ W X) (I.comap W.subtype) :=
  (source_internal_module d h hF9all hcentral hcomm hsource hH K hKH hK a hI).faithfulOrbit_source

/-- F.9.18(1--3) on the same source action, seed and edge actor. -/
theorem source_component_inputs
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H) :
    ∃ (a : Five.StarAction H (Source.UH H V₃) V₁) (B : Subgroup G)
      (I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁))),
      IsIrrPlusWith (linearAction a)
        (componentOrbit (Source.starImage H K) (starSylow H T (le_sup_right.trans hH.1.2)))
        (starSylow H T (le_sup_right.trans hH.1.2)) I ∧
      ChapterD.Section03.InternalModuleHypotheses KnownSimple.IsKnownSimple
        (linearAction a) (starSylow H T (le_sup_right.trans hH.1.2))
        (componentOrbit (Source.starImage H K) (starSylow H T (le_sup_right.trans hH.1.2))) I ∧
      B ≤ ((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 ∧ B ≤ T ∧
      QuadraticMember (linearAction a) (Source.starImage H B) ∧
      Source.starImage H B ⊓ centralizer
        (Source.starImage H (conjugateSpanBy K (T : Subgroup G)) : Set (Source.Hstar H)) = ⊥ ∧
      ∀ X : Subgroup (Source.Hstar H), Source.starImage H K ≤ X → Source.starImage H T ≤ X →
        F918.SpanActorResult (linearAction a) (Source.starImage H B) X I := by
  obtain ⟨a, B, hB, hBT, hq, hf, hspan⟩ :=
    F918.source_component_span_actors d h hF9all hcentral hcomm hsource hH K hKH hK hgen
  obtain ⟨I, hI⟩ := source_homogeneous_seed d h hF9all hcentral hcomm hsource hH K hK a
  refine ⟨a, B, I, hI,
    source_internal_module d h hF9all hcentral hcomm hsource hH K hKH hK a hI,
    hB, hBT, hq, hf, ?_⟩
  apply hspan I
  rw [star_orbit_eq H K T hKH (le_sup_right.trans hH.1.2)]
  exact hI.isIrrPlus

end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
