module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.FirstResidual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.PointOrbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.PointSource

/-!
# The original triangle's reselected first residual and point centralizer

The source recognition constructs the actual swapped natural module in both
orientations. The rank-one covering theorem strengthens the omega-center
placement to equality with K₀. Containment of the original Cartan in the new
vertex makes it a Cartan there as well; its orbit then places all of K in
the centralizer of the reselected point.

Cartan containment in the new vertex, the common second residual, component
placement and triangle generation remain local obligations of
qt-d-1222-shadow-component-triangle. The earlier normalized 7.0.1, 3.2.5,
fixed-line identity and full 11.3.2 inputs retain their final discharge with
qt-d-1222-shadow-components.
Source: Aschbacher–Smith, 11.1.2(3), p.764, and 11.4.1(2), p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open Chapter12.Section02 LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the swapped natural flag in either orientation and identify
its first residual with the actual K₀, using only the preceding source
recognition and shadow implications. -/
theorem exists_triangle_source_flag_first
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
              K₀ ≤ centralizer (f_I.Vi 0 : Set G) ∧ f_I.Li 0 = K₀) := by
  obtain ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I, hm⟩ :=
    exists_triangle_source_flag_point D S f K X htriangle hKnormal hKZ
  refine ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I, ?_⟩
  intro h701 h325
  obtain ⟨S_I, hd, c_I, f_I, hinner, hpoint⟩ := hm h701 h325
  refine ⟨S_I, hd, c_I, f_I, hinner, ?_⟩
  intro h1132
  have hp := hpoint h1132
  exact ⟨hp.1, (local_eq_flag_residual D_I S_I f_I 0 K₀ hK hp.2).symm⟩

/-- Relative normality and Cartan transfer give the whole component's point
centralization once X lies in I. No swapped Hall condition or assertion
that the original K lies in I is required. -/
theorem ofFlag_component_centralizes_reselected_point
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (hd : S.field.degree = 2) (hinner : f.IsInnerUnique) (K K₀ X : Subgroup G)
    (hKnormal : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (hX : LocalGeometry.IsCartan T L X)
    {U : Subgroup G} (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U)
    (S_I : D_I.NonbinaryNaturalInput)
    {c_I : LocalGeometry.Coordinates D_I S_I.field} (f_I : LocalGeometry.InvariantFlag c_I)
    (hd_I : S_I.field.degree = 2) (ho : TriangleOrientation L (K₀ ⊔ f.Li 1))
    (h1132_I : ∀ H, Hypothesis1131At D_I S_I (c_I.binarySubspace (f_I.space 0)) H →
      Proposition1132At D_I S_I (c_I.binarySubspace (f_I.space 0)) H)
    (hfixed : f_I.Vi 0 = U ⊓ centralizer (LocalGeometry.sourceTL T (K₀ ⊔ f.Li 1) : Set G))
    (hXI : X ≤ K₀ ⊔ f.Li 1) :
    K ≤ centralizer (f_I.Vi 0 : Set G) := by
  have hXK : X ≤ normalizer (K : Set G) :=
    (f.cartan_normalizes hinner hX 0).trans
      ((normal_subgroupOf_iff_le_normalizer hKnormal.1.1).mp hKnormal.2)
  exact component_centralizes_point_of_cartan D_I S_I f_I
    (fixed_trivial_of_triangle_order D_I S_I hd_I ho _ h1132_I)
    hfixed K X (cartan_transfer D S hd hX D_I S_I hd_I hXI) hXK hKZ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
