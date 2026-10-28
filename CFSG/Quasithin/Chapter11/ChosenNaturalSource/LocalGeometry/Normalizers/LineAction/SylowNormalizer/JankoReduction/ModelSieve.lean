module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.RankTwoComplete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.OddRankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.OddPrime

/-!
# Applying the model exclusions to the actual moved component

The preceding geometric and odd-action arguments exclude every alternating,
rank-one, rank-two, binary linear, and odd PSL₂ row of Theorem C in the
literal component quotient. Thus a Theorem C model of that quotient must
belong to the odd linear/unitary three-dimensional or sporadic rows, or be
J₁. This is a reduction of the catalogue, not the missing classification
input or the recognition of J₁.

The original normalizer escape supplies the same moved component in the last
application. The task qt-d-1222-natural-line-action retains the classification
input, the remaining model exclusions, intersection escape, and terminal
geometry. Source: Aschbacher--Smith 3.3.12, using A.3.6 and A.3.12.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The A₅ row is incompatible with the proper nonsolvable residual image. -/
theorem quotient_not_alternating_five :
    ¬ IsAlternating (E.component ⧸ pCore 2 E.component) 5 := by
  rintro ⟨e⟩
  exact E.residualImage_not_solvable
    (alternatingGroup.isSolvable_subgroup_of_equiv_five e E.residualImage E.residualImage_ne_top)

/-- The exact odd PSL₂ parameter family in Theorem C is excluded. -/
theorem quotient_not_odd_linear {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hn : n = 1 ∨ n = 2) :
    ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) 2 (p^n) := by
  rcases hn with rfl | rfl
  · simpa only [pow_one] using E.quotient_not_odd_prime_psl2 hp ho
  · exact E.quotient_not_odd_square_psl2 hp ho

/-- The remaining simple-model rows, applied to K/O₂(K) itself. -/
theorem theoremC_remaining
    (h : TheoremCModel (E.component ⧸ pCore 2 E.component)) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool,
      IsPSLSign (E.component ⧸ pCore 2 E.component) unitary 3 p) ∨
    (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((E.component ⧸ pCore 2 E.component) ≃* name.Carrier)) ∨
    Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Janko1.Model) := by
  cases h with
  | alternating n hn iso =>
    have he : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases he with rfl | rfl | rfl | rfl
    · exact (E.quotient_not_alternating_five iso).elim
    · exact (E.quotient_not_alternating_six iso).elim
    · exact (E.quotient_not_alternating_seven iso).elim
    · exact (E.quotient_not_alternating_eight iso).elim
  | linear_odd p n hp ho hn _ iso => exact (E.quotient_not_odd_linear hp ho hn iso).elim
  | three_odd p hp ho unitary iso => exact .inl ⟨p,hp,ho,unitary,iso⟩
  | rank_one iso => exact (E.quotient_not_bender iso).elim
  | rank_two iso => exact (E.quotient_not_rank_two iso).elim
  | binary_linear n hn iso => exact (E.quotient_not_binary_linear (.inr hn) iso).elim
  | sporadic name hne iso => exact .inr (.inl ⟨name,hne,iso⟩)
  | janko_one iso => exact .inr (.inr iso)
end MovedComponent

/-- The escape application uses the same literal component for the entire sieve. -/
theorem exists_moved_component_theoremC_sieve (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      TheoremCModel (E.component ⧸ pCore 2 E.component) →
      (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool,
        IsPSLSign (E.component ⧸ pCore 2 E.component) unitary 3 p) ∨
      (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
        Nonempty ((E.component ⧸ pCore 2 E.component) ≃* name.Carrier)) ∨
      Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Janko1.Model) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.theoremC_remaining⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
