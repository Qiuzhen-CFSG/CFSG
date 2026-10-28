module

public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.Twisted
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.SmallDerivedCovers

/-!
# The Parrott lifting calculation in the B.1.13 consumer

The compatible presentation lifts remove the universal-kernel premise of the
existing small-derived Tits recognition theorem. The consumer starts with the
literal central quotient and ends with the whole Parrott group. The 37-relation
lifting calculation is still explicit; this is a conditional source application.

Sources: Aschbacher–Smith B.1.13, printed pp.73–74, and I.1.3, printed p.407.
-/

public section

namespace CFSG.Quasithin.ChapterI.LieMultipliers.Twisted

open PerfectCentralCovering

/-- The actual B.1.13 Tits covering reduction consumes the Parrott relation
lifts and requires no separate multiplier assumption. -/
theorem tits_recognition_of_lifted_relations
    (hlifts : ∃ g : Tits.ParrottGenerator → UniversalGroup Tits.ParrottGroup,
      Tits.SatisfiesParrottRelations g ∧
        ∀ i, universalProjection Tits.ParrottGroup (g i) = Tits.parrottGenerator i)
    {L : Type*} [Group L] [Group.IsPerfect L]
    (hmodel : Nonempty (L ⧸ Subgroup.center L ≃* Tits.ParrottGroup)) :
    Nonempty (L ≃* Tits.ParrottGroup) :=
  ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.tits_recognition_of_universalKernel
    (tits_universalProjection_ker_eq_bot_of_lifts hlifts) hmodel

end CFSG.Quasithin.ChapterI.LieMultipliers.Twisted
