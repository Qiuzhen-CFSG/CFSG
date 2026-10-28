module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.NormIdeal

/-!
# Conditional exclusion of absolute HS degree forty

The permitted fixed-space hypothesis annihilates the actual five-center norm.
The finite algebra certificate in `NormIdeal` would then bound the squared
degree by a number strictly below 1600, contradicting degree forty.

The certificate still has to be constructed. This module proves only the
conditional implication and does not assert `fixedFreeAbsoluteDegreeFortyExcluded`.
Final assembly belongs here when that finite calculation is complete.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph, author-preprint p.16; Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow

universe v

/-- The finite binary-algebra certificate implies the precise source contract
for every coefficient-field universe. Its construction remains an obligation. -/
theorem fixedFreeAbsoluteDegreeFortyExcluded_of_normCertificate
    (C : FortyExclusion.NormCertificate) : FixedFreeAbsoluteDegreeFortyExcluded.{v} := by
  intro hs K _ _ _ W _ _ _ τ hf hi hfix hd
  have hb := FortyExclusion.finrank_sq_le_certificate_size C τ hi hfix
  rw [hd] at hb
  have := C.size_lt
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow
