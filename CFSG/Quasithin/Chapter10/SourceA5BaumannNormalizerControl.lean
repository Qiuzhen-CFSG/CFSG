module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.NaturalThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedM24
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedJ4
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedHeld

/-!
# Baumann normalizer containment for the original alternating-five setup

The zero-center branch is already excluded in the original escaping reduction.
In positive center, the actual strict overcomponent either has a contained
layer, forcing the forbidden A₇ quotient, or retains a deleted-five block.
The surviving simple central quotient has now been reduced to three sporadic
carriers. Their native local obstructions apply to its literal block and full
Sylow, completing the contradiction without an additional source premise.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original alternating-five setup has Baumann normalizer inside its prescribed maximal local. -/
theorem source_a5_baumann_normalizer_le
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  by_contra hout
  obtain ⟨t,ht,htn,p,hv,hS,I,hLI,hIX,hI,hNI,hseven,hqtk,hO,hq,S,hSm,
    hB,hSB,htop,hproper,hrad,hradiso,hnatural,hsimple,hmodel,hC,hSC,hCblock,hCproper,
    name,hname,iso⟩ := source_a5_original_natural_survivor_three_sporadics D e hn hout
  let := hq
  let := hsimple
  let Sbb := (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))).mapSurjective
    (QuotientGroup.mk'_surjective (center (I ⧸ pCore 2 I)))
  rcases hname with hm | hj | hh
  · subst name
    obtain ⟨a⟩ := iso
    exact SourceEmbeddings.alternatingFiveDeleted_not_m24 a Sbb _ hCblock hC hSC
  · subst name
    obtain ⟨a⟩ := iso
    exact SourceEmbeddings.alternatingFiveDeleted_not_j4 a Sbb _ hCblock hC hSC
  · subst name
    obtain ⟨a⟩ := iso
    exact SourceEmbeddings.alternatingFiveDeleted_not_held a Sbb _ hCblock hSC

end CFSG.Quasithin.Chapter10
