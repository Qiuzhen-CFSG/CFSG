module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.AllIntersections
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Source

/-!
# Small-offender assembly after the complete fixed-space argument

The odd-prime intersection theorem completes the geometric input in every
source row. The full/local natural recognition in the moving local Thompson
branch was proved earlier. Consequently the only remaining model work is
selection of a contained natural or numerically large row when J(T)
centralizes the original local module. Minimality preserves the full module;
the uniform fixed-space theorem excludes the large alternative. The earlier
terminal natural contradiction supplies w≥2.

The quiet model selection remains owned by qt-d-10-nona5-small-offender.
HalfSylowUniqueAt has its existing producer qt-d-10-nona5-half-sylow-unique,
with final discharge by qt-d-10-nona5-point-control. These are explicit
remaining premises, so this does not assert the unconditional source theorem.
Source: Aschbacher--Smith 10.1.1--2 and10.2.10--12, pp.741--742,753--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual small-offender contract from source model bounds and the
independently owned half-Sylow theorem; all geometric callbacks are discharged. -/
theorem nonnormalSmallOffender_of_modelBounds_and_halfSylow
    (hmodels : ModelBoundsAt T) (hhalf : PointControl.HalfSylowUniqueAt T) :
    SourceNonnormalSmallOffenderAt T :=
  NaturalCorank.nonnormalSmallOffender_of_recognition_halfSylow
    (FixedSpaces.recognition_of_models_and_halfSylowUnique hmodels hhalf) hhalf

/-- Moving local Thompson modules already have their actual natural row.
Only the quiet local branch still needs a source model selection. -/
theorem modelBoundsAt_of_quiet_models_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
          (Nonempty (SourceLinearThreeGeometry T E) ∨ Nonempty (LargeModuleBounds E))) :
    ModelBoundsAt T := by
  intro L D g c
  right
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · exact hquiet L D g c hJ
  · exact ⟨D,le_rfl,Or.inl (natural_geometry_of_local_thompson D c hJ
      (PointControl.component_normalizer_le_of_halfSylowUnique D c.nonnormal
        (hhalf c.many L D c.nonnormal c.notA5)))⟩

/-- Uniform geometry and the terminal contradiction are applied to the
original survivor; the remaining quiet row need not assume naturality. -/
theorem nonnormalSmallOffender_of_quiet_models_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
          (Nonempty (SourceLinearThreeGeometry T E) ∨ Nonempty (LargeModuleBounds E))) :
    SourceNonnormalSmallOffenderAt T :=
  nonnormalSmallOffender_of_modelBounds_and_halfSylow
    (modelBoundsAt_of_quiet_models_and_halfSylow hhalf hquiet) hhalf

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
