module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank

/-!
# The higher-rank FF splitting consumer and its replacement

Thompson replacement supplies a quadratic minimal best offender inside the
given Sylow subgroup. The two faithful factors retain the source budget and,
in the dual orientation, force rank at least four. Independently, the extension
matrix calculation supplies quadratic common-center root pairs in the original actors.

The ambient axis four-group now discharges all B.4.9(1) hypotheses in either
quotient orientation, so its authorized implication splits the actual
extension. The four-group need not lie inside the replacement: a rank-six
minimal offender on two split natural modules can contain no transvections.
The source consumer below retains the original Sylow containment and the
replacement's two-factor budget. Source: Aschbacher–Smith B.4.9(2)(i),
printed pp.92–95. The independent B.4.9(1) implication remains explicit.
-/

public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {F : BinaryField} {n : ℕ}
  {ρ : Representation (ZMod 2) G V}

/-- Actual B.4.9(2) dual input: replacement, its two-factor budget, and the
ambient quadratic root identities, all on the original representation. -/
theorem dual_ff_reduction (d : DoubleNatural F n ρ) (hF : F.degree = 1) (hn : 6 ≤ n)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) (hA : IsBestOffender ρ A)
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual) :
    ∃ B ≤ A, B ≤ (T : Subgroup G) ∧ IsMinimalBestOffender ρ B ∧ IsQuadratic ρ B ∧
      4 ≤ rank B ∧
      fixedCodim d.space.toRepresentation B + fixedCodim d.space.quotientRepresentation B ≤ rank B ∧
      ∀ (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k),
        (ρ ((binaryForm d hF).natural.groupEquiv.symm
          (SpecialLinearGroup.transvection hij 1)) - 1) *
          (ρ ((binaryForm d hF).natural.groupEquiv.symm
            (SpecialLinearGroup.transvection hik 1)) - 1) = 0 := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  obtain ⟨B, hBA, hB, hquad, _⟩ :=
    (hA.isOffender ρ).exists_quadratic_minimalBestOffender ρ
  have hoff := hB.1.isOffender ρ
  exact ⟨B, hBA, hBA.trans hAT, hB, hquad, (d.dual_offender_bounds eQ hoff).2.2,
    d.offender_budget hoff, fun _ _ _ hij hik => degree_one_dual_root_product d hF hn eQ hij hik⟩

/-- The actual higher-dimensional B.4.9(2) input splits, in both quotient
orientations and for every degree-one field carrier. Thompson replacement
remains inside the same best offender and Sylow and satisfies the two-factor
budget. All premises of the authorized splitting implication are discharged. -/
theorem ff_splitting (d : DoubleNatural F n ρ) (hF : F.degree = 1) (hn : 6 ≤ n)
    (splitting : ∀ d' : DoubleNatural F n ρ,
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) (hA : IsBestOffender ρ A) :
    d.Splits ∧ ∃ B ≤ A, B ≤ (T : Subgroup G) ∧ IsMinimalBestOffender ρ B ∧
      IsQuadratic ρ B ∧ 2 ≤ rank B ∧
      fixedCodim d.space.toRepresentation B +
        fixedCodim d.space.quotientRepresentation B ≤ rank B := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  obtain ⟨B, hBA, hB, hquad, _⟩ :=
    (hA.isOffender ρ).exists_quadratic_minimalBestOffender ρ
  have hoff := hB.1.isOffender ρ
  exact ⟨d.binary_higher_splits hF hn splitting, B, hBA, hBA.trans hAT, hB, hquad,
    d.offender_rank_ge_two hoff, d.offender_budget hoff⟩
end CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
