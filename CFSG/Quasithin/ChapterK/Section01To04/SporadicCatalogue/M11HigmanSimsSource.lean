module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceM11
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHSDegreeComplete
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHSOuterPairs

/-!+# The M₁₁ and Higman–Sims exclusions on the cubic source domain

This module exports both exclusions for the original finite ambient actor,
faithful binary representation and irreducible generalized Fitting action.
The M₁₁ proof uses its marked eleven-point module. For HS, five-conjugate
generation bounds the degree by fifty, the complete binary degree window
forces degree twenty, and the inner and both outer estimates contradict the
small-displacement cubic actor. All degree, cover and action inputs are proved.

The marked-component application transports the literal equality with F*(G),
so it retains the given central-quotient marking and ambient action.

Source: Aschbacher--Smith K.4, printed p.457/PDF p.468, citing Guralnick--Malle,
Classification of 2F-modules I, Theorem 6.6/Table 6.7; the HS calculations are
in Proposition 5.1, published pp.366--367 (author-preprint pp.16--17).
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Subgroup
universe u v

/-- HS cannot be the marked central quotient of the actual generalized
Fitting subgroup under the original Chapter K cubic source hypotheses. -/
theorem sourceExclusion_hs : SourceExclusion.{u,v} .hs :=
  sourceExclusion_hs_of_degree_and_outer higmanSimsDegreeWindow higmanSims_outer_estimates

/-- Apply the unconditional HS exclusion through the original component's
equality with F*(G), preserving its actual central-quotient marking. -/
theorem not_hs_of_rankOne_source
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier)) : False := by
  rcases h.fitting with rfl
  exact sourceExclusion_hs ρ
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩ he

end CFSG.Quasithin.ChapterK.SporadicCatalogue
