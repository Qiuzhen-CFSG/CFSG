module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Alternating
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.FixedComponent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Branches

/-!
# Screening the full central-quotient catalogue in E.6.23

The alternating branch is proved, using faithful descent, the strict order
bound, the seven-letter involution calculation, and the actual A₈–PSL₄(2)
equivalence. The binary-linear branch is already the desired alternative.
The actual embedded A₆ remains a component of an involution centralizer
on the quotient, supplying precisely the input to the odd and Bender
calculations. The remaining rank-two and sporadic branches retain the
whole source configuration and every clause of the earlier statements.

The theorem below is conditional on the outstanding exclusions in `Branches`.
It does not yet prove `QuotientRecognition` without those premises. The
unconditional source assembly remains owned by this module.

Source: Aschbacher–Smith, Theorem C, printed p.33, and the further-enlargement
paragraph of E.6.23, p.254 (PDF p.265), combined manuscript of 1 March 2004.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
open QuotientScreen
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M V : Subgroup G}

/-- The complete catalogue reduces to the remaining intrinsic and source-specific
model calculations. All action and component premises are proved from the input. -/
theorem quotientRecognition_of_model_exclusions [IsElementaryAbelian 2 V]
    (hodd : OddFixedComponentExclusion.{u})
    (hbender : BenderFixedComponentExclusion.{u})
    (hrank : RankTwoExclusion T M V) (hsporadic : SporadicExclusion T M V) :
    QuotientRecognition T M V := by
  intro h h15 earlier U A L X g d hne Y hY hm
  let _ := extension_quasisimple hY
  let _ : IsSimpleGroup (Y ⧸ center Y) := IsQuasisimple.simple
  let _ : Group.IsPerfect (Y ⧸ center Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Y))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨a, ha, hS, hsix⟩ := quotient_fixed_six_component d hY
  cases hm with
  | alternating n hn e =>
      exact Or.inl (alternating_quotient d hY hn e.some)
  | odd ho =>
      exact (hodd _ ho a ha _ hS hsix).elim
  | bender hb =>
      exact (hbender _ hb a ha _ hS hsix).elim
  | rank_two f hf =>
      exact (hrank h h15 earlier U A L X g d hne Y hY f hf).elim
  | linear_binary n hn he =>
      rcases hn with rfl | rfl
      · exact Or.inl he
      · exact Or.inr he
  | sporadic hs =>
      exact (hsporadic h h15 earlier U A L X g d hne Y hY hs).elim

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
