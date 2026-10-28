module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.DoubleNaturalSplitting
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.DegreeOne
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFour
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.DualGeometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank

/-!
# B.4.9(2) on the two natural factors of the B.5.1 induction

The proved quadratic splitting theorem discharges the last earlier premise
of all existing FF branches. Every positive SL₃ field degree is included,
and every binary dimension at least four. The SL₃ orientation and ratio,
the dimension-four Thompson group, and all dimension-five parabolic alternatives
retain the original actor and quotient maps.

Source: Aschbacher--Smith, B.4.9(2), printed pp.94--95; its applications
in B.5.1, printed pp.101--102.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
open NaturalExtensions NaturalExtensions.QuadraticSplitting
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  {F : BinaryField} {n : ℕ}

/-- B.4.9(2)(i)--(ii), for every binary defining field and the literal natural submodule. -/
theorem doubleNatural_three_ff (d : DoubleNatural F 3 ρ) (hff : IsFFModule ρ) :
    d.Splits ∧ Nonempty (d.space.quotientRepresentation.Equiv d.space.toRepresentation) ∧
      quadraticRatio ρ = 1 := by
  classical
  by_cases hF : F.degree = 1
  · exact d.degree_one_three_ff hF hff
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  obtain ⟨A, hA⟩ := hff
  obtain ⟨B, _, hB⟩ := hA.exists_bestOffender ρ
  obtain ⟨T, hT⟩ := (show IsPGroup 2 B from hB.1.2.isPGroup 2 B).exists_le_sylow
  exact d.larger_field_three_ff (by have hp := F.degree_pos; omega)
    (fun d' hh => doubleNatural_splits d' hh) T hT hB

/-- B.4.9(2)(i),(iii), with the original Sylow and its elementary Thompson subgroup. -/
theorem doubleNatural_four_dual_ff (d : DoubleNatural F 4 ρ) (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (hA : IsBestOffender ρ A) :
    d.Splits ∧ A = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ∧
      rank A = 4 ∧ quadraticRatio ρ = 1 :=
  d.binary_four_dual_ff hF (doubleNatural_splits d) e T hAT hA

/-- B.4.9(2)(i),(iv), retaining the exact end-node and interior-node placements. -/
theorem doubleNatural_five_dual_ff (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (hA : IsBestOffender ρ A) :
    d.Splits ∧ quadraticRatio ρ = 5 / 6 ∧ DoubleNatural.BinaryFive.DualAlternatives d hF A :=
  DoubleNatural.BinaryFive.dual_ff d hF T doubleNatural_splits e hAT hA

/-- B.4.9(2)(i) in the complete source family. No splitting or classification
premise remains; the result gives a complement to the original natural layer. -/
theorem doubleNatural_ff_splits (d : DoubleNatural F n ρ)
    (hfamily : SourceFamily F n) (hff : IsFFModule ρ) : d.Splits := by
  classical
  rcases hfamily with hn | ⟨hF, hn⟩
  · subst n
    exact (doubleNatural_three_ff d hff).1
  by_cases h4 : n = 4
  · subst n
    exact d.binary_four_ff hF (doubleNatural_splits d) hff
  by_cases h5 : n = 5
  · subst n
    let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
    obtain ⟨A, hA⟩ := hff
    obtain ⟨B, _, hB⟩ := hA.exists_bestOffender ρ
    obtain ⟨T, hT⟩ := (show IsPGroup 2 B from hB.1.2.isPGroup 2 B).exists_le_sylow
    rcases d.quotient with ⟨e⟩ | ⟨e⟩
    · obtain ⟨e⟩ := e
      exact DoubleNatural.BinaryFive.SameAxis.splits_of_bestOffender
        d hF e T doubleNatural_splits hT hB
    · obtain ⟨e⟩ := e
      exact (doubleNatural_five_dual_ff d hF e T hT hB).1
  exact d.binary_higher_splits hF (by omega) doubleNatural_splits

/-- The actual B.5.1 moved-module application. The original FF hypothesis
supplies an offender on the moved subrepresentation by fixed-codimension
monotonicity; the induction supplies its two literal natural layers. -/
theorem moved_doubleNatural_splits [Finite G] {K : GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (d : DoubleNatural F n s.space.toRepresentation) (hf : SourceFamily F n) : d.Splits := by
  obtain ⟨A, hA⟩ := ExtensionConsequences.source_isFF h
  exact doubleNatural_ff_splits d hf
    ⟨A, hA.1, (fixedCodim_subrepresentation_le ρ s.space A).trans hA.2⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
