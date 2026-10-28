module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.SourceCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Mathieu
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.MathieuPair
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue

/-!
# The source catalogue after the Mathieu and Held exclusions

The full Sylow normalizer and outer automorphism calculations also exclude
Held. Thus the only remaining sporadic simple carriers are J₂, HS, Ru, J₄
and J₁. The M₂₂ central-cover exclusion removes the last sporadic covering
row. This refinement keeps the actual component two-core quotient, the odd
classical cubic covers, both nonquasisimple alternatives, and all A.3.6
common data. The original escaping supplement supplies the component in
the final application.

Source: Aschbacher–Smith 3.3.12, argument (**), printed p.589, using A.3.6.
Recognition, intersection escape and terminal geometry remain with
qt-d-1222-natural-line-action.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- The surviving sporadic names; each use below also carries a literal isomorphism. -/
def RemainingSporadicName (name : ClassificationModels.SporadicName) : Prop :=
  name = .j2 ∨ name = .hs ∨ name = .ru ∨ name = .j4

/-- The refined full A.3.6 cases, with the covering and nonquasisimple data intact. -/
inductive SourceCasesAfterSporadicSieve (Q : Type*) [Group Q] [Finite Q] : Prop
  | simple (simple : IsSimpleGroup Q)
      (model : (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsPSLSign Q unitary 3 p) ∨
        (∃ name : ClassificationModels.SporadicName, RemainingSporadicName name ∧
          Nonempty (Q ≃* name.Carrier)) ∨ Nonempty (Q ≃* Janko1.Model))
  | cover (quasisimple : IsQuasisimple Q)
      (center : Nonempty (Subgroup.center Q ≃* Multiplicative (ZMod 3)))
      (model : ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsSLSign Q unitary 3 p)
  | natural (data : A36Natural (⊤ : Subgroup Q))
  | nilpotent (data : A36Nilpotent (⊤ : Subgroup Q))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The actual Held carrier has a self-normalizing Sylow and two-group outer quotient. -/
theorem quotient_not_held :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Held.He) :=
  E.quotient_not_equiv_self_normalizing_outer_two
    Held.LocalPairs.SylowGeometry.Calculations.inner_self_normalizing
    (Subgroup.isPGroup_outer_of_normalizer Held.permutationGroup 2
      Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient)

/-- Every actual sporadic isomorphism in the source catalogue has a surviving name. -/
theorem remaining_sporadic_name (name : ClassificationModels.SporadicName) (hne : name ≠ .j3)
    (hm : Nonempty ((E.component ⧸ pCore 2 E.component) ≃* name.Carrier)) :
    RemainingSporadicName name := by
  cases name with
  | m11 => exact (E.quotient_not_mathieu_eleven hm).elim
  | m12 => exact (E.quotient_not_mathieu_twelve hm).elim
  | m22 => exact (E.quotient_not_mathieu_twentyTwo hm).elim
  | m23 => exact (E.quotient_not_mathieu_twentyThree hm).elim
  | m24 => exact (E.quotient_not_mathieu_twentyfour hm).elim
  | j2 => exact .inl rfl
  | hs => exact .inr (.inl rfl)
  | ru => exact .inr (.inr (.inl rfl))
  | j4 => exact .inr (.inr (.inr rfl))
  | j3 => exact (hne rfl).elim
  | he => exact (E.quotient_not_held hm).elim

/-- Full source refinement without a simple-model premise or a discarded center. -/
theorem source_cases_after_sporadic_sieve :
    SourceCasesAfterSporadicSieve (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨hc,hcommon⟩ := E.remaining_source_cases
  refine ⟨?_,hcommon⟩
  cases hc with
  | simple hs hm =>
    apply SourceCasesAfterSporadicSieve.simple hs
    rcases hm with h | ⟨name,hne,he⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨name,E.remaining_sporadic_name name hne he,he⟩)
    · exact .inr (.inr h)
  | cover hq hz hm =>
    apply SourceCasesAfterSporadicSieve.cover hq hz
    cases hm with
    | classical p hp ho u hi => exact ⟨p,hp,ho,u,hi⟩
    | mathieu hi => exact (E.quotient_not_mathieu_cover hi).elim
  | natural h => exact .natural h
  | nilpotent h => exact .nilpotent h

end MovedComponent

/-- The original escaping normalizer supplies the very component to which every
model exclusion and every surviving source clause applies. -/
theorem exists_moved_component_after_sporadic_sieve (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      SourceCasesAfterSporadicSieve (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.source_cases_after_sporadic_sieve⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
