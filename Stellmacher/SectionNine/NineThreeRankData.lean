module
public import Stellmacher.SectionNine.NineThreeNormalizedGeometry
public import Stellmacher.SectionFiveToSeven.SixFourRankActionSetup
public import Stellmacher.SectionOne.SmallFixedIndexRank

/-!
# Retained canonical rank data for the intermediate wreath branch

The shared proposition records the exact elementary module instance, canonical
quotient action hypotheses, nontrivial critical subgroup, unique maximality,
Sylow generation, zero fixed complement, two canonical factors and center order
sixteen used in the intermediate (9.3) branch. Each action-dependent field uses
the named Section Six quotient action. The historical public record name is
preserved for its native-action wrappers; the canonical proof also constructs
it directly from barred critical nontriviality.

Source: Stellmacher (1.7) and (9.3), Journal of Algebra 190 (1997), p.50,
`refs/files/stellmacher-n-group.pdf`. These are intermediate data for wreath
recognition and the subsequent centralizer contradiction, not numbered (9.3).
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- The actual canonical quotient inputs and rank-two conclusion after the
native-action branch of (9.3). Every action-dependent field retains the
named Section Six action. -/
public structure NineThreeNativeActionRankData
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) : Prop where
  elementary : IsElementaryAbelian 2 (sectionSixLocalV ctx.hypothesisTwo)
  center_card : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 16
  critical_ne_bot : sectionSixBarredCritical ctx.hypothesisTwo ≠ ⊥
  action_hypotheses :
    letI := elementary
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    SectionOne.Hypotheses (SectionSixBarP1 ctx.hypothesisTwo)
      (sectionSixLocalV ctx.hypothesisTwo)
  unique_maximal : IsUniqueMaximalContaining
    (sectionSixBarSylow ctx.hypothesisTwo : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) ⊤
  generated :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    SectionOne.oneE (V := sectionSixLocalV ctx.hypothesisTwo)
      (sectionSixBarSylow ctx.hypothesisTwo : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) ⊔
        (sectionSixBarSylow ctx.hypothesisTwo : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) = ⊤
  fixed_product_eq_bot :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    FixedPoints.subgroup (SectionOne.oneE (V := sectionSixLocalV ctx.hypothesisTwo)
      (sectionSixBarSylow ctx.hypothesisTwo : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)))
        (sectionSixLocalV ctx.hypothesisTwo) = ⊥
  factor_count :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    (SectionOne.oneSevenFactors (G := SectionSixBarP1 ctx.hypothesisTwo)
      (V := sectionSixLocalV ctx.hypothesisTwo)).card = 2


end Stellmacher.SectionNine
