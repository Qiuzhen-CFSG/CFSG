module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Branches
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.FixedComponent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.KnownOrders

/-!
# Assembly of the full sporadic quotient exclusion

M₁₁, M₂₃ and J₁ are excluded unconditionally using their concrete orders
and involution fixed subgroups. The remaining seven non-HS models require
their involution-centralizer calculations. HS retains the full ambient
source configuration, because its inner involution table really contains
an A₆ component. All eleven entries of C(5) are retained.

The assembly below is conditional on those remaining calculations. It does
not claim the unconditional sporadic branch of E.6.23. Simplicity and
perfectness of each concrete model are transported from Y/Z(Y).

Source: Aschbacher–Smith, Theorem C, printed p.33, E.6.8, pp.247–248,
E.6.18, p.252, and the further enlargement in E.6.23, p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M V : Subgroup G}

/-- Assemble all eleven source entries, with the remaining model calculations
explicit. The three proved cases and all source-to-model transfers are discharged. -/
theorem sporadicExclusion_of_remaining [IsElementaryAbelian 2 V]
    (hfixed : ∀ name : SporadicName,
      name ≠ .m11 → name ≠ .m23 → name ≠ .j3 → name ≠ .hs →
      IsSimpleGroup name.Carrier → Group.IsPerfect name.Carrier →
        Sporadic.FixedSixExclusion name.Carrier)
    (hHS : Sporadic.SourceExclusion _root_.Sporadic.LeechRelated.HS.Carrier T M V) :
    SporadicExclusion T M V := by
  intro h h15 earlier U A L X g d hne Y hY hm
  rcases hm with ⟨name, hname, ⟨e⟩⟩ | ⟨e⟩
  · by_cases h11 : name = .m11
    · subst name
      exact Sporadic.not_quotient_of_fixed_exclusion Sporadic.m11 d hY e
    by_cases h23 : name = .m23
    · subst name
      exact Sporadic.not_quotient_of_fixed_exclusion Sporadic.m23 d hY e
    by_cases hhs : name = .hs
    · subst name
      exact hHS h h15 earlier U A L X g d hne Y hY ⟨e⟩
    exact Sporadic.sourceExclusion_of_fixed_exclusion
      (hfixed name h11 h23 hname hhs) T M V
      h h15 earlier U A L X g d hne Y hY ⟨e⟩
  · exact Sporadic.not_quotient_of_fixed_exclusion Sporadic.janko_one d hY e.some

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
