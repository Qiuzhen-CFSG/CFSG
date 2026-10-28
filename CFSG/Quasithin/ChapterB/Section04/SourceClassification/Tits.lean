module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.Source

/-!
# Excluding the Tits constructor on the literal B.4 source domain

The original quasisimple generalized Fitting subgroup has the specified Tits
central quotient. Its perfect cover is identified by the proved covering
comparison; the unconditional cubic exclusion then applies to the original
faithful binary action and arbitrary ambient elementary actors. A best
offender supplies the source cubic bound through the existing replacement
argument.

Source: Aschbacher--Smith B.4.2 and K.3, printed pp.86 and 457.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The Tits central quotient is excluded already at the full cubic threshold. -/
theorem tits_exclusion (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (e : L ⧸ center L ≃* Tits.ParrottGroup) : False := by
  let : L.Normal := h.fitting ▸ inferInstance
  let := h.quasisimple
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  exact ChapterK.Exceptional.TitsCubicDisplacement.source_centralQuotient_exclusion
    ρ L e h.faithful h.smallCubic

/-- Literal B.4 best-offender application to the actual Theorem C Tits model. -/
theorem not_tits_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (e : L ⧸ center L ≃* Tits.ParrottGroup) : False :=
  tits_exclusion (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA) e

end CFSG.Quasithin.ChapterB.SourceClassification
