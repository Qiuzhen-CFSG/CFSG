module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.Reduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.CentralExtension
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.Offenders

/-!
# Odd-degree SL₃ comparison on the literal seed

`ThreeCovers.natural_or_fourDimensionalCover` proves the central-extension
dichotomy on U itself. A zero central denominator gives the actual natural
L-action. Otherwise the natural-module cohomology calculation forces degree
one, and the universal-cover kernel bound gives dimension four. The imported
central-extension proof establishes indecomposability and the actual reduced
natural action before applying the complete B.4.8(2) implication.

`compared_linearThree_of_source` assembles the two resulting `ComparedCase`
constructors. Offender generation and the B.5.1 extension alternatives identify
the component image with the whole faithful seed quotient. This gives inner
action on the original L in both branches. In the cover branch, the literal
offender image is Klein four, the quotient ratio is one, and the original Irr⁺,
centralizer disjointness and rank equality complete the comparison.

The full universal `CentralExtension.EarlierB48Two` remains an explicit
earlier-source input, owned by `qt-b-04-natural-extensions` / `qt-b-04` and
discharged finally by `qt-b05-general-classification`. The full-moved-space
hypothesis is supplied by `qt-b05-compared-double-three` and discharged by
`qt-b05-preliminary-source-comparison`, which also owns the exhaustive row
assembly. No local extension classification, U=[V,L], or A≤L is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.107; B.4.8(2), printed p.91; I.1.6(4), printed p.408.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

namespace ThreeCovers

/-- The central-extension dichotomy on the original L-action on U. The
exceptional branch retains degree one and every clause of B.4.8(2). -/
theorem natural_or_fourDimensionalCover (h48 : CentralExtension.EarlierB48Two.{u,v})
    {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      s.space.toSubmodule)
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype)
      (linearNatural F 3)) :
    Nonempty (ActionEquiv (seedComponentAction ρ hLA) (linearNatural F 3)) ∨
      (F.degree = 1 ∧ Nonempty (FourDimensionalCoverSource (seedComponentAction ρ hLA))) := by
  by_cases hz : fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊥
  · exact Or.inl ⟨transAction (seedComponentActionEquiv ρ hLA p)
      (naturalOfWholeSection s hm hz e)⟩
  · have hF : F.degree = 1 := by
      have hnot : ¬ 1 < F.degree := fun h =>
        hz (seed_fixed_eq_bot_of_large ρ hLA p s hm hi F h e)
      have hpos := F.degree_pos
      omega
    exact Or.inr ⟨hF,
      CentralExtension.seed_fourDimensionalCover ρ h48 hLA p s hm F hF e hz⟩

end ThreeCovers

/-- Compare the actual irreducible SL₃ source row with the literal seed.
The source fields are exactly those of `RankOneActionCase.irreducible` and
`RankOneIrreducibleCase.linearThree`. The only earlier-source parameter is
the full B.4.8(2) implication; the cohomology and all local cover premises
are proved. Final assembly supplies the independently proved moved equality. -/
theorem compared_linearThree_of_source
    (h48 : ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) (hr : primeRank 3 L = 1)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      c.sectionData.space.toSubmodule)
    (hf : Function.Injective c.sectionData.action)
    (hir : IsIrreducible (c.sectionData.action.comp (seedComponentImage ρ hLA).subtype))
    (hext : seedComponentImage ρ hLA = ⊤ ∨
      (∀ T : Sylow 2 (SeedQuotient ρ hLA),
        seedComponentImage ρ hLA ⊔ (T : Subgroup (SeedQuotient ρ hLA)) = ⊤) ∧
      OuterNaturalAction c.sectionData.action)
    (F : BinaryField) (ho : Odd F.degree)
    (hg : offenderSubgroup c.sectionData.action = seedComponentImage ρ hLA)
    (e : ActionEquiv (c.sectionData.action.comp (seedComponentImage ρ hLA).subtype)
      (linearNatural F 3))
    (hq : quadraticRatio c.sectionData.action = 1 / 2) : ComparedCase ρ hLA := by
  have htop := ThreeCovers.seedComponentImage_eq_top ρ hLA p c.sectionData hm hi hf hir
    hext F hg e hq
  have hinner : InducesInner A L := by
    apply inducesInner_of_seedOffenderImage_le ρ hLA p
    rw [htop]
    exact le_top
  rcases ThreeCovers.natural_or_fourDimensionalCover ρ h48 hLA p c.sectionData hm hi F e
      with hn | ⟨_, hc⟩
  · obtain ⟨natural⟩ := hn
    exact .naturalThree F ho natural hinner
  · obtain ⟨cover⟩ := hc
    exact .fourCover cover
      (ThreeCovers.seedOffenderImage_klein_of_cover ρ hLA p htop cover)
      (ThreeCovers.seed_irrPlus ρ hLA c.sectionData hm hi) hinner
      (seed_disjoint_of_source ρ hLA p hr c)
      (ThreeCovers.seedRankEquality_of_cover ρ hLA p htop cover)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
