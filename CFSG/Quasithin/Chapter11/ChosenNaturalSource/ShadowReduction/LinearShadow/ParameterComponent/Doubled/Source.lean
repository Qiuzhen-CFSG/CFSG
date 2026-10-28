module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.PointCentralizers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Statements

/-!
# Source parameter exclusion from the preceding generation alternative

The exact 11.2.1 alternative supplies the original doubled module and k≤2n.
Its SL₃ branch is excluded by the complete doubled geometry and reciprocal
contradiction. A competing Sp₄ or G₂ marking has a different dimension on
the same literal central quotient. Hence k≤n for the original invariant flag.
The component consumer combines this with the preceding lower bound.

The generation alternative is still owned by
qt-d-1222-natural-weak-closure-source. Its construction is not asserted here.
The authorized RankOneReduction and earlier lower-bound discharge remain
with qt-d-1222-shadow-parameter-component. The present source task retains
final assembly after its generation prerequisite is available.

Source: Aschbacher--Smith, 11.3.6 and 11.3.7(1), printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

private theorem seed_fixed_corank (c : LocalGeometry.Coordinates D S.field) :
    ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) =
      S.field.degree * Module.finrank S.field.Carrier c.Space := by
  rw [← c.preimage_bot,LocalGeometry.WeakClosure.Parameters.NaturalDimensions.pullback_corank D S c]
  rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule S.field.Carrier c.Space) rfl).finrank_eq]

/-- The strict-parameter branch is excluded using the actual preceding
11.2.1 alternative. That source theorem has its existing independent owner;
there is no remaining doubled geometry or numerical callback. -/
theorem source_parameter_upper (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : RankOneReduction S H)
    (hgen : LocalGeometry.WeakClosure.Generation.Conclusion D S H) :
    ChapterE.generationParameter H ≤ S.field.degree := by
  rcases hgen with hu | ⟨_,d,_,_,hu⟩
  · exact hu
  have dc : Coordinates D S := d
  obtain ⟨m,hm⟩ := dc
  have hdim := seed_fixed_corank (LocalGeometry.Coordinates.sl3 m)
  rw [LocalGeometry.WeakClosure.Parameters.NaturalDimensions.field_dimension] at hdim
  change ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) = S.field.degree*3 at hdim
  cases c with
  | sl3 m' =>
    exact (source_doubled_contradiction h p hc ⟨m,hm⟩ m' f hpoint r hu).elim
  | sp4 m' =>
    have hh := seed_fixed_corank (LocalGeometry.Coordinates.sp4 m')
    rw [LocalGeometry.WeakClosure.Parameters.NaturalDimensions.field_dimension] at hh
    change ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) = S.field.degree*4 at hh
    have := S.field.degree_pos
    omega
  | g2 m' =>
    have hh := seed_fixed_corank (LocalGeometry.Coordinates.g2 m')
    rw [LocalGeometry.WeakClosure.Parameters.NaturalDimensions.field_dimension] at hh
    change ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) = S.field.degree*6 at hh
    have := S.field.degree_pos
    omega

/-- Apply the strict-parameter exclusion to the actual outside residual
component, preserving its quotient, relative normality and Sylow supplement. -/
theorem source_parameter_component (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (hpoint : c.binarySubspace (f.space 0) = U₁)
    (r : RankOneReduction S H)
    (hgen : LocalGeometry.WeakClosure.Generation.Conclusion D S H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ParameterComponent.Conclusion S H :=
  assemble_of_parameter_upper h p hc r hs (source_parameter_upper h p hc f hpoint r hgen)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
