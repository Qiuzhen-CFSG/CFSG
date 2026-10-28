module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.PointPlacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Exclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag

/-!
# Constructing the reselected source flag and its first residual containment

The actual field-four triangle selects I = K₀ ∨ L₂ and a chosen Irr⁺ module.
The genuine earlier 7.0.1 and 3.2.5 outputs recognize this same module. Its
natural marking constructs an inner-Sylow-unique invariant flag in either
orientation. The full 11.3.2 implication removes the central fixed space;
the source [Z,K] = 1 then places K₀ in the first flag residual.

This proves a containment, not the still-needed equality of the first
residual with K₀ or the common second residual with L₂. Those constructions
and triangle generation remain in `qt-d-1222-shadow-component-triangle`.
`qt-d-1222-shadow-components` retains final discharge of the earlier
7.0.1, 3.2.5, 11.1.2 and 11.3.2 source premises.
Source: Aschbacher--Smith, 11.1.2(3), p.764, and 11.4.1(2), p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open Chapter12.Section02 LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the swapped flag from the original triangle choice, in both
orientations, and place the actual K₀ in its first residual. Only preceding
source implications remain conditional; no chosen module or flag is assumed. -/
theorem exists_triangle_source_flag_point
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K X : Subgroup G)
    (htriangle : FieldFourTriangle T L (f.Li 0) (f.Li 1) K X)
    (hKnormal : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G)) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      TriangleOrientation L (K₀ ⊔ f.Li 1) ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T (K₀ ⊔ f.Li 1) ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U),
        Chapter7.NormalizedSource.Alternatives G D_I.orbitRepresentation D_I.orbitComponent →
        D_I.Source325Alternatives →
        ∃ S_I : D_I.NonbinaryNaturalInput, S_I.field.degree = 2 ∧
          ∃ (c_I : LocalGeometry.Coordinates D_I S_I.field)
            (f_I : LocalGeometry.InvariantFlag c_I), f_I.IsInnerUnique ∧
            ((∀ H, Hypothesis1131At D_I S_I (c_I.binarySubspace (f_I.space 0)) H →
                Proposition1132At D_I S_I (c_I.binarySubspace (f_I.space 0)) H) →
              K₀ ≤ centralizer (f_I.Vi 0 : Set G) ∧ K₀ ≤ f_I.Li 0) := by
  obtain ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I, hm⟩ :=
    Classification.exists_triangle_source_marking D S f K X htriangle hKnormal
  refine ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I, ?_⟩
  intro h701 h325
  obtain ⟨S_I, hd, hmark⟩ := hm h701 h325
  rcases hmark with ⟨_, ⟨m⟩⟩ | ⟨_, ⟨m⟩⟩
  · let f_I := LocalGeometry.Sp4.flag m S_I
    refine ⟨S_I, hd, .sp4 m, f_I, LocalGeometry.Sp4.flag_inner_unique m S_I, ?_⟩
    intro h1132
    exact triangle_other_le_firstResidual D_I S_I f_I rfl hK hle hKZ
      (fixed_trivial_of_triangle_order D_I S_I hd ho _ h1132)
  · let f_I := LocalGeometry.G2.flag S_I m
    refine ⟨S_I, hd, .g2 m, f_I, LocalGeometry.G2.flag_inner_unique S_I m, ?_⟩
    intro h1132
    exact triangle_other_le_firstResidual D_I S_I f_I rfl hK hle hKZ
      (fixed_trivial_of_triangle_order D_I S_I hd ho _ h1132)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
