module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Contracts
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Numerics
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Parabolics

/-!
# Dimension-five FF extensions: bounds and conditional assembly

The elementary-rank bound and both interior-parabolic alternatives are proved
on the original marked group. Splitting constructs a literal strict offender
and hence gives the exact dual ratio 5/6. The source splitting implication is
applied to a quadratic four-group with a common axis on the actual quotient.
Thompson replacement reduces its construction to minimal best offenders
inside the given Sylow subgroup.

The final theorem in this module is explicitly conditional: the construction
of this four-group in each orientation and the rank-four end-node Levi
placement are still geometric inputs. It is not the completed B.4.9(2).
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(2)(i),(iv), printed pp.94–95.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)

include hF in
/-- In degree one and dimension five there are no exceptional root-group
or four-element-field clauses to discharge. The full source contract is used. -/
theorem sourceHypotheses_of_axisFour (h : HasQuadraticAxisFour d) :
    QuadraticSplitting.SourceHypotheses d := by
  obtain ⟨E, hE, hq⟩ := h
  refine ⟨Or.inr ⟨hF, by decide⟩, ⟨E, hE, hq, ?_⟩, ?_⟩
  · intro he
    norm_num at he
  · intro he
    omega

include hF in
/-- Apply the exact B.4.9(1) implication only after its actual four-group
and upstairs quadraticity have been supplied. -/
theorem splits_of_axisFour
    (splitting : ∀ d' : DoubleNatural F 5 ρ,
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (h : HasQuadraticAxisFour d) : d.Splits :=
  splitting d (sourceHypotheses_of_axisFour d hF h)

variable [FiniteDimensional (ZMod 2) V]

/-- Replacement preserves containment in the source's actual Sylow group,
and the geometric witness is allowed to lie outside the original offender. -/
theorem axisFour_of_minimal_witnesses (T : Sylow 2 G)
    (geometry : ∀ B : Subgroup G, B ≤ (T : Subgroup G) →
      IsMinimalBestOffender ρ B → IsQuadratic ρ B → HasQuadraticAxisFour d)
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G)) (hA : IsBestOffender ρ A) :
    HasQuadraticAxisFour d := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  obtain ⟨B, hBA, hB, hq, _⟩ :=
    (hA.isOffender ρ).exists_quadratic_minimalBestOffender ρ
  exact geometry B (hBA.trans hAT) hB hq

/-- Only the rank-four end-node placement remains beyond the established
rank bound and the literal interior-parabolic geometry. -/
theorem dual_alternatives_of_rank_four
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hfour : rank A = 4 → EndNodePlacement d hF A) : DualAlternatives d hF A := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  rcases dual_rank_cases d hF e (hA.isOffender ρ) with h | h | h
  · exact Or.inl ⟨h, hfour h⟩
  · exact Or.inr ⟨Or.inl h, interior_parabolic_placement d hF hA.1 (by omega)⟩
  · exact Or.inr ⟨Or.inr h, interior_parabolic_placement d hF hA.1 (by omega)⟩

/-- Conditional assembly on a genuine `DoubleNatural` consumer and its
Sylow offender. The two witness constructions and the rank-four Levi
placement remain explicit; the rank, ratio and interior alternatives do not. -/
theorem ff_of_geometric_inputs (T : Sylow 2 G)
    (splitting : ∀ d' : DoubleNatural F 5 ρ,
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (same : d.space.quotientRepresentation.Equiv d.space.toRepresentation →
      ∀ B : Subgroup G, B ≤ (T : Subgroup G) →
        IsMinimalBestOffender ρ B → IsQuadratic ρ B → HasQuadraticAxisFour d)
    (dual : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual →
      ∀ B : Subgroup G, B ≤ (T : Subgroup G) →
        IsMinimalBestOffender ρ B → IsQuadratic ρ B → HasQuadraticAxisFour d)
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G)) (hA : IsBestOffender ρ A)
    (four : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual →
      rank A = 4 → EndNodePlacement d hF A) :
    d.Splits ∧
      (d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual →
        quadraticRatio ρ = 5 / 6 ∧ DualAlternatives d hF A) := by
  have haxis : HasQuadraticAxisFour d := by
    rcases d.quotient with h | h
    · obtain ⟨e⟩ := h
      exact axisFour_of_minimal_witnesses d T (same e) hAT hA
    · obtain ⟨e⟩ := h
      exact axisFour_of_minimal_witnesses d T (dual e) hAT hA
  have hs := splits_of_axisFour d hF splitting haxis
  exact ⟨hs, fun e => ⟨dual_ratio_of_splits d hF e hs,
    dual_alternatives_of_rank_four d hF e hA (four e)⟩⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
