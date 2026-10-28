module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.DegreeWindows
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion.Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion.PointGeometry
public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source

/-!
# Excluding M₁₁ on the original cubic source domain

The finite perfect central-cover theorem removes the center. The degree window
and the unconditional small-module recognition identify the component action
with the marked eleven-point module. Its rank-two fixed codimension is at least
five, contradicting the codimension four forced by the source cubic actor.
All maps and ambient extensions are retained by the existing marked assembly.

Source: Aschbacher--Smith, K.4, printed p.457/PDF p.468, citing
Guralnick--Malle, Theorem 6.6 and Table 6.7.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup
open _root_.Sporadic.Mathieu
universe u v

/-- The degree-twelve M₁₁ exclusion with all three model inputs discharged. -/
theorem boundedSourceExclusion_m11 : BoundedSourceExclusion.{u,v} .m11 12 := by
  exact boundedSourceExclusion_m11_of_inputs.{u,v} (by
    intro L _ _ _ e
    rw [← PerfectCentralCovering.centralQuotientCover_ker e]
    exact SchurMultipliers.m11_cover_kernel_eq_bot
      (PerfectCentralCovering.centralQuotientCover e))
    M11Exclusion.smallDegreeRecognition M11Exclusion.rankTwoPointGeometry

/-- M₁₁ cannot be the marked central quotient of the actual generalized
Fitting subgroup under the original Chapter K cubic source hypotheses. -/
theorem sourceExclusion_m11 : SourceExclusion.{u,v} .m11 :=
  sourceExclusion_m11_of_bounded boundedSourceExclusion_m11

/-- Transport the genuine marked-component interface through its F* equality. -/
theorem not_m11_of_rankOne_source
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m11.Carrier)) : False := by
  rcases h.fitting with rfl
  exact sourceExclusion_m11 ρ
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩ he

end CFSG.Quasithin.ChapterK.SporadicCatalogue
