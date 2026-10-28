module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.Reduction
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.AxisFourGeometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source

/-!
# Assembly of the larger-field SL₃ FF branch

The proved reduction constructs a quadratic full axis actor inside the original
best offender, identifies the literal quotient with the original natural
submodule, and gives quadratic ratio one. Two independent shears in that actor
supply the source four-group outside every root group. Special-linear conjugacy
of the full axis groups supplies the global quadraticity clause over F₄.
The final application therefore needs only the exact B.4.9(1) splitting
implication, whose proof remains with its independent source owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(2)(i)–(ii), printed pp.92–94.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource
namespace DoubleNatural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V} (d : DoubleNatural F 3 ρ)

/-- A geometry-parametrized assembly on the original module. The theorem
`larger_field_three_ff` below supplies this premise from the full axis actor. -/
theorem larger_field_three_ff_of_axis_geometry (hF : 1 < F.degree)
    (hSplit : ∀ {m : ℕ} (d' : DoubleNatural F m ρ),
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (T : Sylow 2 G)
    (hGeometry : 1 < F.degree →
      ∀ (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
        (B : Subgroup G), B ≤ T → IsQuadratic ρ B →
        IsFullAxisGroup F 3 (B.map (d.threeQuotientAction e).groupEquiv.toMonoidHom) →
        QuadraticSplitting.SourceHypotheses d)
    {A : Subgroup G} (hAT : A ≤ T) (hA : IsBestOffender ρ A) :
    d.Splits ∧ Nonempty (d.space.quotientRepresentation.Equiv d.space.toRepresentation) ∧
      quadraticRatio ρ = 1 := by
  obtain ⟨e, B, hBA, _, hq, _, _, haxis⟩ := d.three_full_axis_replacement hA
  have hBT : B ≤ T := hBA.trans hAT
  have hsource := hGeometry hF e B hBT hq haxis
  exact ⟨hSplit d hsource, ⟨e⟩, d.three_ratio ⟨A, hA.isOffender ρ⟩⟩

/-- B.4.9(2)(i)–(ii) for the larger-field SL₃ branch, conditional only on the
exact universal B.4.9(1) implication. The original best offender supplies a
quadratic full axis subgroup inside the given Sylow group. Its source four-group,
root exclusion, and the global F₄ clause are all proved before applying splitting.
Both module factors and the resulting complement retain their original markings. -/
theorem larger_field_three_ff (hF : 1 < F.degree)
    (hSplit : ∀ {m : ℕ} (d' : DoubleNatural F m ρ),
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) (hA : IsBestOffender ρ A) :
    d.Splits ∧ Nonempty (d.space.quotientRepresentation.Equiv d.space.toRepresentation) ∧
      quadraticRatio ρ = 1 := by
  apply d.larger_field_three_ff_of_axis_geometry hF hSplit T ?_ hAT hA
  intro _ e B _ hq haxis
  exact d.three_sourceHypotheses_of_full_axis e hq haxis

end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
