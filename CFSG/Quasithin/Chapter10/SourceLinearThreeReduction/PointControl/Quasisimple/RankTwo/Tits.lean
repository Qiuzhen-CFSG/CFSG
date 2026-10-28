module
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.CarrierReduction

/-!
# Excluding the Tits containing component

The literal proper image of L is a local C-component at the full restricted
Sylow. After the actual Parrott-to-Atlas equivalence, all proper full-Sylow
overgroups are solvable, so this local C-component would equal the whole
simple central quotient. That contradicts its established properness.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
No module marking, A₅ quotient or generation bound is needed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The proper local C-component cannot lie in a Tits central quotient:
its full-Sylow overgroup would be solvable. -/
theorem not_tits [IsQuasisimple I]
    (e : (I ⧸ center I) ≃* Tits.ParrottGroup) : False := by
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsQuasisimple (I ⧸ center I) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center I)) (QuotientGroup.mk'_surjective (center I))
  obtain ⟨S,_,hB,_,_,hproper,_⟩ := center_quotient_data D c
  have ht : (⊤ : Subgroup (I ⧸ center I)).IsCComponent :=
    (show IsComponent (I ⧸ center I) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  apply hproper
  apply SourceEmbeddings.eq_of_solvable_sylow_overgroups
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) hB ht le_top
  exact SolvableSylowOvergroups.of_equiv (topEquiv.trans e)
    Tits.ProperSylowOvergroups.solvableSylowOvergroups
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
