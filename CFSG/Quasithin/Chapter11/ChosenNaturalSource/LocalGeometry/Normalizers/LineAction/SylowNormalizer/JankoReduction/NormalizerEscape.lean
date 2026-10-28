module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.FlagNormalizers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.IntersectionAction

/-!
# Escape from the ambient component normalizer in the recognized J₁ case

The checked product A = (K intersect A) N_A(Y) forces K intersect A to move
the original flag residual Y when K/O₂(K) is J₁. If that intersection
normalized L, it would be an odd subgroup normalizing both T and L. The
actual two-parabolic geometry would then make it normalize Y, a
contradiction. This proves escape from N_G(L), and supplies the last
normalizer-escape field of the literal terminal configuration.

The source application preserves the full remaining A.3.6 alternatives and
common data. Its J₁ branch constructs the terminal configuration with no
separate escape premise. Recognition of that branch and its remaining
terminal geometry, as well as the G₂ line-action branch, remain with
qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.12(3b), 3.3.15--16, printed pp.589--591;
the final line-action consumer is 11.2.3, pp.768--769.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- For the actual odd component intersection, movement of Y forces escape
from the ambient normalizer of L. -/
theorem intersection_escapes_of_moves
    (hmoves : ¬ E.component ⊓ A.subgroup ≤ normalizer (f.Li E.index : Set G)) :
    ¬ E.component ⊓ A.subgroup ≤ normalizer (L : Set G) := by
  intro hL
  have ho : Odd (Nat.card (E.component ⊓ A.subgroup : Subgroup G)) :=
    A.odd.of_dvd_nat (card_dvd_of_le inf_le_right)
  exact hmoves (odd_normalizes_flag_residual f _ ho
    (inf_le_right.trans A.normalizes) hL E.index)

/-- Certified J₁ innerness and the actual odd supplement force escape from
N_G(L), rather than merely movement of the chosen residual. -/
theorem janko_intersection_escapes
    (e : E.component ⧸ pCore 2 E.component ≃* Janko1.Model) :
    ¬ E.component ⊓ A.subgroup ≤ normalizer (L : Set G) :=
  E.intersection_escapes_of_moves (E.janko_intersection_moves e)

/-- The actual recognized J₁ quotient constructs all fields of the
terminal configuration, including escape, from the original moved component. -/
def recognizedJankoConfiguration
    (e : E.component ⧸ pCore 2 E.component ≃* Janko1.Model) :
    JankoConfiguration S f A :=
  E.jankoConfiguration e (E.janko_intersection_escapes e)

/-- Application to the literal section-centralizer displacement used in
the common-normal terminal argument. Only its remaining geometry is explicit. -/
theorem false_of_janko_common_normal
    (e : E.component ⧸ pCore 2 E.component ≃* Janko1.Model)
    (hne : (E.recognizedJankoConfiguration e).oddSectionCentralizer ≠ ⊥)
    (hLQ : L ≤ normalizer ((E.recognizedJankoConfiguration e).displacement : Set G)) :
    False :=
  (E.recognizedJankoConfiguration e).false_of_displacement_normalized_by_L hne hLQ

/-- Application to the literal small displacement used in the second
terminal argument, with the normalizer-escape premise discharged. -/
theorem false_of_janko_small_displacement
    (e : E.component ⧸ pCore 2 E.component ≃* Janko1.Model)
    (hsmall : Nat.card (E.recognizedJankoConfiguration e).displacement ≤ 2 ^ 16)
    (hmoves : ¬ f.Li E.index ≤
      centralizer ((E.recognizedJankoConfiguration e).displacement : Set G)) : False :=
  (E.recognizedJankoConfiguration e).false_of_small_moved_displacement hsmall hmoves

end MovedComponent

/-- The source catalogue and common data stay on the same moved component.
Its recognized J₁ branch now supplies the full literal terminal configuration,
with actual K intersect A escape proved rather than assumed. -/
theorem exists_moved_component_with_janko_configuration
    (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      SourceCasesAfterLargeSporadic (E.component ⧸ pCore 2 E.component) ∧
      Chapter1.Section02.A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) ∧
      (Nonempty (E.component ⧸ pCore 2 E.component ≃* Janko1.Model) →
        ∃ J : JankoConfiguration S f A,
          J.index = E.index ∧ J.component = E.component) := by
  obtain ⟨E,hcases,hcommon⟩ := exists_moved_component_after_large_sporadic f A hescape
  refine ⟨E,hcases,hcommon,?_⟩
  rintro ⟨e⟩
  exact ⟨E.recognizedJankoConfiguration e,rfl,rfl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
