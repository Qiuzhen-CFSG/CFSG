module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion.Intrinsic
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion.OuterBound

/-!
# The full triple-seven exclusion in K.1

A faithful irreducible binary module for the genuine triple cover of A₇ has
degree at least twelve. The elementary conjugate-generation budget in A₇
forces degree at most eight when its cubic ratio is at most two, proving the
intrinsic exclusion. For an ambient extension, every elementary actor of
ratio at most two lies in the component: the dimension bound excludes
inversion of its central cubic subgroup, and the normalizer calculation
places each center-fixing involution inside the component.

Transporting the resulting cubic actor through the actual component
isomorphism discharges the full `Input` contract. The theorem is independent
of the Recognition assembly, which can consume it without an import cycle.

Source: Aschbacher–Smith, K.1, printed p.452/PDF p.463, invoking
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

public section
namespace CFSG.Quasithin.ChapterK.Alternating
universe u v

/-- The genuine triple cover of A₇ is excluded under the full Chapter K
hypotheses, including possible outer ambient extensions. -/
theorem tripleSevenExclusion : RecognitionInputs.TripleSevenExclusion.{u,v} :=
  tripleSevenExclusion_of_intrinsic tripleSevenIntrinsicExclusion
    tripleSevenRestrictionBound

end CFSG.Quasithin.ChapterK.Alternating
