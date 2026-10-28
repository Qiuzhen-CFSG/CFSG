module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Completion.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.NaturalDual

/-!+# Small-offender assembly with the natural-plus-dual row removed

The quiet-row selector may now return the actual natural-plus-dual marking.
Its six-dimensional bounds and the uniform fixed-space contradiction exclude
that row, including after contained seed reselection. The original assembly
then supplies the literal natural geometry and the lower bound w≥2.

Quiet-row selection remains owned by qt-d-10-nona5-small-offender.
HalfSylowUniqueAt retains its producer qt-d-10-nona5-half-sylow-unique and
ultimate discharge by qt-d-10-nona5-point-control. Both remain explicit here;
this theorem does not assert the unconditional source conclusion.

Source: Aschbacher--Smith 10.1.1(5) and 10.2.12, pp.741,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original small-offender consumer after the actual natural-plus-dual
row has been discharged, retaining the remaining quiet selection premise. -/
theorem nonnormalSmallOffender_of_quiet_rows_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
          (Nonempty (SourceLinearThreeGeometry T E) ∨
            Nonempty (LargeModuleBounds E) ∨ NaturalDualRow E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_models_and_halfSylow hhalf
  intro L D g c hJ
  obtain ⟨E,hE,hrow⟩ := hquiet L D g c hJ
  rcases hrow with hnatural | hlarge | hdual
  · exact ⟨E,hE,Or.inl hnatural⟩
  · exact ⟨E,hE,Or.inr hlarge⟩
  · exact (no_contained_natural_dual_of_small_offender D c E hE hdual
      (PointControl.component_normalizer_le_of_halfSylowUnique D c.nonnormal
        (hhalf c.many L D c.nonnormal c.notA5))).elim

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
