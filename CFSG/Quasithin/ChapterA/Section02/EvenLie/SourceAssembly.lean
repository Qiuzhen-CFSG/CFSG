module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.ClassicalSimple
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.CubicCovers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankTwoCovers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.SymplecticSimple
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalSimple
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.ReeCovers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.UnitaryFourCover
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankTwoSimple
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.SmallDerived
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalBinary
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.Exceptional
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankOneAliases
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.HigherLinear
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.SymplecticCovers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalMinus
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.UnitaryFiveFourCover
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.HigherUnitary
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalCovers

/-!
# Completed source branches of the even-characteristic Lie-family dispatch

All six classical families are resolved in both original source cases, at
every catalogue parameter. G2, Suzuki, triality, ReeF4 and all small-derived
models are also resolved. F4, E6, E7 and twisted E6 are excluded in both
cases, including field order two. All covering conclusions preserve the
original central quotient and proper-section induction.

The E8 section is the only remaining input to the exhaustive A.2.18 dispatch.
Its concrete root-operator producer is being checked separately.
Source: Aschbacher--Smith A.2.13 and A.2.18, printed pp.38 and 40.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G : Type u} [Group G] [Finite G]

/-- The actual linear Case I contradicts the source minimal-counterexample choice. -/
theorem not_minimalCounterexample_linear [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {d a : ℕ} (ha : 0 < a)
    (hp : KnownSimple.LinearParameters d (2 ^ a))
    (iso : ClassicalGroup.IsPSL G d (2 ^ a)) : False := by
  obtain ⟨_, hqt, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_linear hqt ha hp iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The actual unitary Case I contradicts the source minimal-counterexample choice. -/
theorem not_minimalCounterexample_unitary [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {d a : ℕ} (ha : 0 < a)
    (hp : KnownSimple.UnitaryParameters d (2 ^ a))
    (iso : ClassicalGroup.IsPSU G d (2 ^ a)) : False := by
  obtain ⟨_, hqt, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_unitary hqt ha hp iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
