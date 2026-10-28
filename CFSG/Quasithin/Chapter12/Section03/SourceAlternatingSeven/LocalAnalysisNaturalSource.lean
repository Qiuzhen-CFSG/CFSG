module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNatural
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionSelection
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisFusion

/-!
# Original Lemma 12.3.3 on the full chosen A₇ module

The central-line residual and block argument force a proper C-component
in the four-dimensional row. Every nonsplit moved-module alternative is
excluded: the classical parabolics cannot contain the surviving PSL₃(2)
section, the small rows fail the order and Sylow constraints, and the A₈
augmentation core contradicts the literal normalizer two-core bound.

The remaining natural quotient lifts across the original perfect central
cover by cohomology and V=[V,L]. Its full marking is aligned with the
setup's original O₂,Z quotient. Thus all of V has natural coordinates,
with no exceptional-exclusion or splitting premise. The final application
supplies these coordinates to the existing local-analysis constructor;
its Sylow-normalizer and point-centralizer premises belong to the later
12.3.4–8 assembly, owned by qt-d-1231-local-analysis.

Source: Aschbacher–Smith, Lemma 12.3.3, printed pp.807–808.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- Original 12.3.3: the entire original V is the natural A₇ module,
intertwining the original L-conjugation with the specified central quotient. -/
theorem naturalCoordinates_nonempty
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : Nonempty S.NaturalCoordinates :=
  S.naturalCoordinates_of_four_exclusion modules (S.four_false structural escape)

/-- A full marking supplied by the proved source theorem. -/
def naturalCoordinates
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : S.NaturalCoordinates :=
  Classical.choice (S.naturalCoordinates_nonempty structural modules escape)

/-- The actual local-analysis consumer, now with the natural-coordinate
premise discharged by original 12.3.3. The later centralizer premises remain
with the section's local-analysis assembly owner. -/
def localAnalysis_of_natural_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hpoints : let E := S.naturalCoordinates structural modules escape
      ∀ v : V, v ≠ 1 →
        (weight (E.coordinates v).toAdd.val = 2 ∨
          weight (E.coordinates v).toAdd.val = 6) →
        centralizer ({(v:G)} : Set G) ≤ normalizer (L : Set G)) : S.LocalAnalysis :=
  (S.naturalCoordinates structural modules escape).localAnalysis structural hNT hpoints

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
