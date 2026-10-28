module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFour.ThompsonGeometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source
public import Theory.Representation.BinaryOffender.QuadraticFourSpace
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# The binary dimension-four FF branch of B.4.9

Thompson replacement supplies a quadratic best offender of rank at most four.
Below rank four, the two-factor budget forces the quotient fixed space to be
a hyperplane. At rank four, the faithful quadratic quotient action fills its
two-space radical, so displacement constructs an actual common-axis four-group.
Both orientations thus satisfy every hypothesis of B.4.9(1).

The splitting implication remains the authorized premise, supplied by the
source assembly. The dual branch additionally identifies A with the source
Thompson subgroup of the original Sylow and proves rank four and ratio one.
Every degree-one field carrier is covered without changing the original
representation, natural submodule or quotient.
Source: Aschbacher–Smith B.4.9(2)(i),(iii), combined manuscript of 1 March 2004,
printed pp.92,94.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource QuadraticSplitting
namespace DoubleNatural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 4 ρ)

/-- The literal quotient is a four-dimensional binary space over every degree-one carrier. -/
theorem binary_four_quotient_finrank (hF : F.degree = 1) :
    Module.finrank (ZMod 2) (V ⧸ d.space.toSubmodule) = 4 := by
  have hd := d.finrank
  rw [hF] at hd
  have hs := d.space.toSubmodule.finrank_quotient_add_finrank
  have hq := d.quotient_finrank
  omega

/-- Rank-four replacement supplies the source four-subgroup on the actual quotient,
in either orientation. Quadraticity is inherited from the original extension. -/
theorem binary_four_axis_of_rank_four (hF : F.degree = 1)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : rank A = 4) (hq : IsQuadratic ρ A) :
    ∃ E : Subgroup G, E ≤ A ∧ IsAxisFour d E ∧ IsQuadratic ρ E := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  have hq' : IsQuadratic d.space.quotientRepresentation A :=
    quadratic_of_equivariant_surjection ρ d.space.quotientRepresentation d.space.toSubmodule.mkQ
      d.space.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hq
  obtain ⟨E, hEA, he, hc, I, hI, hfix⟩ := QuadraticFourSpace.rank_four_axis
    d.space.quotientRepresentation d.quotient_faithful (d.binary_four_quotient_finrank hF)
      A hA hr hq'
  exact ⟨E, hEA, ⟨he, hc, I, hI.trans hF.symm, hfix⟩,
    fun a ha b hb v => hq a (hEA ha) b (hEA hb) v⟩

/-- Below rank four the two-factor budget forces a common quotient hyperplane.
The dual orientation is excluded by its lower rank bound. -/
theorem binary_four_axis_of_rank_lt_four (hF : F.degree = 1)
    {A : Subgroup G} (hA : IsOffender ρ A) (hr : rank A < 4) (hq : IsQuadratic ρ A) :
    ∃ E : Subgroup G, E ≤ A ∧ IsAxisFour d E ∧ IsQuadratic ρ E := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  rcases d.quotient with he | he
  · obtain ⟨e⟩ := he
    have heq : fixedCodim d.space.quotientRepresentation A =
        fixedCodim d.space.toRepresentation A := by
      simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
        d.space.quotientRepresentation d.space.toRepresentation (MonoidHom.id G)
          e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A
    have hbudget := d.offender_budget hA
    have hp := (d.factor_costs_pos hA.1.1).2
    have hc : fixedCodim d.space.quotientRepresentation A = 1 := by omega
    obtain ⟨E, hEA, he, hcard, I, hI, hfix⟩ := QuadraticFourSpace.fixed_hyperplane_axis
      d.space.quotientRepresentation d.quotient_faithful A hA.1
        (d.offender_rank_ge_two hA) hc
    exact ⟨E, hEA, ⟨he, hcard, I, hI.trans hF.symm, hfix⟩,
      fun a ha b hb v => hq a (hEA ha) b (hEA hb) v⟩
  · obtain ⟨e⟩ := he
    have := (d.dual_offender_bounds e hA).2.2
    omega

/-- Every binary degree-four FF-extension contains a quadratic four-group
with a common axis on its literal quotient. This is the full hypothesis
construction for B.4.9(1), before invoking that splitting implication. -/
theorem binary_four_quadratic_axis (hF : F.degree = 1) (hff : IsFFModule ρ) :
    ∃ E : Subgroup G, IsAxisFour d E ∧ IsQuadratic ρ E := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  obtain ⟨A, hA⟩ := hff
  obtain ⟨B, _, hB, hq, _⟩ := hA.exists_quadratic_minimalBestOffender ρ
  have hr := d.binary_four_rank_le hF hB.1.1
  have hex : ∃ E : Subgroup G, E ≤ B ∧ IsAxisFour d E ∧ IsQuadratic ρ E := by
    by_cases he : rank B = 4
    · exact d.binary_four_axis_of_rank_four hF hB.1.1 he hq
    · exact d.binary_four_axis_of_rank_lt_four hF (hB.1.isOffender ρ) (by omega) hq
  obtain ⟨E, _, he, hq⟩ := hex
  exact ⟨E, he, hq⟩

/-- The exact B.4.9(1) hypotheses, including its dimension and field clauses,
are consequences of the FF hypothesis in binary degree four. -/
theorem binary_four_splitting_hypotheses (hF : F.degree = 1) (hff : IsFFModule ρ) :
    SourceHypotheses d := by
  obtain ⟨E, he, hq⟩ := d.binary_four_quadratic_axis hF hff
  exact ⟨Or.inr ⟨hF, by decide⟩, ⟨E, he, hq, by omega⟩, by omega⟩

/-- B.4.9(2)(i) for every degree-one field carrier and both quotient orientations.
The only premise beyond the source FF setup is the authorized B.4.9(1) implication. -/
theorem binary_four_ff (hF : F.degree = 1)
    (splitting : SourceHypotheses d → d.Splits) (hff : IsFFModule ρ) : d.Splits :=
  splitting (d.binary_four_splitting_hypotheses hF hff)

/-- The dimension-four dual branch of B.4.9(2)(i),(iii), with the source Thompson
subgroup, original ambient containment and an invariant complement to the given submodule. -/
theorem binary_four_dual_ff (hF : F.degree = 1)
    (splitting : SourceHypotheses d → d.Splits)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (hA : IsBestOffender ρ A) :
    d.Splits ∧ A = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ∧
      rank A = 4 ∧ quadraticRatio ρ = 1 := by
  obtain ⟨hJ, hr, hratio, _⟩ := d.binary_four_dual_geometry hF e T hAT hA
  exact ⟨d.binary_four_ff hF splitting ⟨A, hA.isOffender ρ⟩, hJ, hr, hratio⟩
end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
