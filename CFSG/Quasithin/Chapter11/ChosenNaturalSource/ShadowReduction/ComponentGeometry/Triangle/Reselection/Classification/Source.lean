module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.DoubledExclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Recognition

/-!
# Recognizing the unchanged field-four triangle seed

The earlier 7.0.1 and 3.2.5 source conclusions give FF on the orbit and the
three seed alternatives. B.5.1 excludes a doubled orbit for either triangle
component, so the original seed is T-invariant and FF. Its actual central
quotient is then recognized as the appropriate natural field-four action.

This discharges the swapped chosen-module construction in 11.4.1(2).
The earlier normalized 7.0.1 and source 3.2.5 conclusions are produced by
`qt-d-1222-normalized-nonff` and `qt-baumann-fsu`;
`qt-d-1222-shadow-components` retains their final discharge;
paired flag placement and the final triangle elimination remain with
`qt-d-1222-shadow-component-triangle`.
Source: Aschbacher--Smith 3.2.5, 7.0.1, 11.0.2 and 11.4.1, pp.580,695,759--760,776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02 ChapterB.QuasisimpleSource LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L I U : Subgroup G}

/-- Recognition of the same chosen module, in both source orientations. -/
theorem nonbinary_of_source701325 (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) :
    ∃ S : D.NonbinaryNaturalInput, S.field.degree = 2 := by
  obtain ⟨hTU, hff⟩ := seed_invariant_ff_of_source701325 D h ho h701 h325
  exact nonbinary_of_ff D h ho hmany hTU hff

/-- The swapped symplectic marking uses the very same field as its input. -/
theorem symplectic_marked_of_source701325 (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmodel : Source.IsSp (I ⧸ pCore 2 I) 2 4)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) :
    ∃ S : D.NonbinaryNaturalInput, S.field.degree = 2 ∧ Nonempty
      (ActionEquiv D.centralQuotientAction (binarySymplectic S.field)) := by
  obtain ⟨hTU, hff⟩ := seed_invariant_ff_of_source701325 D h ho h701 h325
  exact symplectic_input_of_ff D h ho hmodel hmany hTU hff

/-- The swapped G₂ marking also retains the input's own field. -/
theorem g2_marked_of_source701325 (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmodel : ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h701 : Chapter7.NormalizedSource.Alternatives G D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) :
    ∃ S : D.NonbinaryNaturalInput, S.field.degree = 2 ∧ Nonempty
      (ActionEquiv D.centralQuotientAction (binaryG2 S.field)) := by
  obtain ⟨hTU, hff⟩ := seed_invariant_ff_of_source701325 D h ho h701 h325
  exact g2_input_of_ff D h ho hmodel hmany hTU hff

/-- The actual source triangle supplies the original choice I = K₀ ∨ L₂;
only the preceding source conclusions remain to recognize that choice. -/
theorem exists_triangle_source_recognition {V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K X : Subgroup G)
    (htriangle : FieldFourTriangle T L (f.Li 0) (f.Li 1) K X)
    (hKnormal : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      TriangleOrientation L (K₀ ⊔ f.Li 1) ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T (K₀ ⊔ f.Li 1) ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U),
        Chapter7.NormalizedSource.Alternatives G D_I.orbitRepresentation D_I.orbitComponent →
        D_I.Source325Alternatives →
        ∃ S_I : D_I.NonbinaryNaturalInput, S_I.field.degree = 2 := by
  obtain ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, ⟨D_I⟩⟩ :=
    exists_triangle_choice D S f K X htriangle hKnormal
  exact ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I,
    nonbinary_of_source701325 D_I hI ho S.many⟩

/-- The actual triangle choice comes with a marking on its own degree-two
field in each orientation. Neither orientation replaces the original seed
or assumes an already natural module. -/
theorem exists_triangle_source_marking {V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K X : Subgroup G)
    (htriangle : FieldFourTriangle T L (f.Li 0) (f.Li 1) K X)
    (hKnormal : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      TriangleOrientation L (K₀ ⊔ f.Li 1) ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T (K₀ ⊔ f.Li 1) ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U),
        Chapter7.NormalizedSource.Alternatives G D_I.orbitRepresentation D_I.orbitComponent →
        D_I.Source325Alternatives →
        ∃ S_I : D_I.NonbinaryNaturalInput, S_I.field.degree = 2 ∧
          ((ClassificationModels.IsG2At (L ⧸ pCore 2 L) 4 ∧ Nonempty
            (ActionEquiv D_I.centralQuotientAction (binarySymplectic S_I.field))) ∨
           (Source.IsSp (L ⧸ pCore 2 L) 2 4 ∧ Nonempty
            (ActionEquiv D_I.centralQuotientAction (binaryG2 S_I.field)))) := by
  obtain ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, ⟨D_I⟩⟩ :=
    exists_triangle_choice D S f K X htriangle hKnormal
  refine ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I, ?_⟩
  intro h701 h325
  rcases ho with ho | ho
  · obtain ⟨S_I, hd, hm⟩ := symplectic_marked_of_source701325 D_I hI
      (Or.inl ho) ho.2 S.many h701 h325
    exact ⟨S_I, hd, Or.inl ⟨ho.1, hm⟩⟩
  · obtain ⟨S_I, hd, hm⟩ := g2_marked_of_source701325 D_I hI
      (Or.inr ho) ho.2 S.many h701 h325
    exact ⟨S_I, hd, Or.inr ⟨ho.1, hm⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
