module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.JankoTwo
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Nonquasisimple
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.OddClassical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.NormalizerEscape

/-!
# Recognition of the actual moved-component quotient

The full A.3.6 source catalogue now has exactly one surviving row. The
odd-action parabolic argument excludes J₂, the central-involution argument
excludes both nonquasisimple rows, and the literal binary residual image
excludes the odd classical groups and their full cubic covers. Together
with the preceding exclusions this identifies K/O₂(K) with the concrete J₁
model, without a recognition hypothesis or a simple-group substitute.

The recognized quotient feeds the existing intersection-escape theorem,
constructing every field of the actual J₁ terminal configuration. In
particular an escaping Sylow normalizer forces field degree two, proving
normalizer containment at all other nonbinary field orders. The field-four
terminal geometry remains with qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.12(3b), 3.3.15--16, printed pp.589--591;
the final line-action application is 11.2.3, pp.768--769.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The full source catalogue recognizes the literal quotient, with no extra model premise. -/
theorem componentQuotient_isJanko :
    Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Janko1.Model) := by
  cases E.source_cases_after_janko_two.1 with
  | simple _ hm =>
    rcases hm with ⟨p,hp,ho,u,hm⟩ | hm
    · exact ((E.quotient_not_odd_classical hp ho u).1 hm).elim
    · exact hm
  | cover _ _ hm =>
    obtain ⟨p,hp,ho,u,hm⟩ := hm
    exact ((E.quotient_not_odd_classical hp ho u).2 hm).elim
  | natural hn => exact (E.quotient_not_natural hn).elim
  | nilpotent hn => exact (E.quotient_not_nilpotent hn).elim

/-- Construct the source configuration, including the actual intersection escape. -/
def sourceJankoConfiguration : JankoConfiguration S f A :=
  E.recognizedJankoConfiguration E.componentQuotient_isJanko.some

end MovedComponent

/-- An escaping Sylow normalizer yields the complete literal J₁ configuration. -/
theorem exists_janko_configuration (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nonempty (JankoConfiguration S f A) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E.sourceJankoConfiguration⟩

/-- All possible escaping configurations occur at field order four. -/
theorem degree_eq_two_of_sylow_normalizer_escape (f : InvariantFlag c)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    S.field.degree = 2 := by
  obtain ⟨A⟩ := oddSupplement_nonempty T
  obtain ⟨E⟩ := exists_janko_configuration f A hescape
  exact E.degree_eq_two

/-- The Sylow normalizer is contained in N_G(L) at every other nonbinary field order. -/
theorem sylow_normalizer_le_of_degree_ne_two (f : InvariantFlag c)
    (hdegree : S.field.degree ≠ 2) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact hdegree (degree_eq_two_of_sylow_normalizer_escape f hescape)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

