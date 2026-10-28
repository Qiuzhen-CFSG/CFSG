module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Inputs
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.Reduction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.PointGeometry

/-!
# Selecting natural-plus-dual coordinates on the actual component commutator

The genuine component is A₈ and contains the conjugate strong offender.
Apply the full B.5.1 conclusion to its actual action. The strong-offender
sieve leaves a natural central quotient, natural plus dual, or repeated
naturals, all in degree four. The actual S₈ extension excludes the first
and third branches by inverse similarity. The second gives coordinates on
`PointData.space` itself, with the canonical projective matrix action and
its contragredient.

`coordinates_of_sourceConclusion` proves coordinate selection from
`SourceSetup`, `ReducedLocalData`, `MiddleNodeEight`, `PointData`, and the
full B.5.1 conclusion. The source-theorem owner supplies that classification
conclusion and retains the separate point-core contradiction. No projection
of B.5.1(6)'s no-offender field is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1145; B.4.2, p.86; B.5.1, pp.99–103.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
open Chapter2.ComponentRefinement.LieType.Binary
open ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve (card_of_alternating)

universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {H M Y V Y₀ L ZS Z A : Subgroup G} {T : Sylow 2 G}
  [IsElementaryAbelian 2 (localSpan ZS H)]
  (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T)
  (r : ReducedLocalData H M L Y₀ T)
  (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T))
  {Vγ : Subgroup G} (p : PointData d Vγ)
  (c : QuasisimpleSourceConclusion (d.action.representation.comp (starImage H L).subtype) ⊤)

include r m p in
/-- The literal component action satisfies the strong-offender A₈ sieve. -/
theorem source_remaining_cases :
    RemainingCases (d.action.representation.comp (starImage H L).subtype) c.sectionData := by
  have hs := strong_subgroupOf d.action.representation (p.strong_alpha d)
    (star_offender_le_component d r)
  exact remaining_cases _ (card_of_alternating (component_alternating m)) ⟨_, hs⟩
    c.sectionData c.clause_one

include r m p in
/-- Conditional assembly with precisely the two natural-branch exclusions
explicit. `coordinates_of_sourceConclusion` discharges both below. -/
theorem coordinates_of_natural_exclusions
    (hquotient : ¬ Nonempty (ActionEquiv
      (c.sectionData.action.comp (⊤ : Subgroup (starImage H L)).subtype)
      (linearNatural BinaryField.two 4)))
    (hrepeated : ∀ k, 0 < k → k ≤ 3 → ¬ IsRepeatedLinearNatural
      (c.sectionData.space.toRepresentation.comp (⊤ : Subgroup (starImage H L)).subtype)
      BinaryField.two 4 k) :
    ∃ e : starImage H L ≃* PSL 4,
      Nonempty (NaturalDualCoordinates d.action.representation (starImage H L) e p.space) := by
  rcases source_remaining_cases d r m p c with hq | hd | ⟨k, hk, hb, hrep⟩
  · exact (hquotient hq).elim
  · exact coordinates_of_naturalDual _ _ p.space p.component_space c.sectionData hd
  · exact (hrepeated k hk hb hrep).elim

include r m p c in
/-- The full B.5.1 conclusion selects actual PSL₄(2) natural-plus-dual
coordinates on the literal component commutator. The S₈ extension excludes
both natural branches, including the possibly nonsplit central quotient. -/
theorem coordinates_of_sourceConclusion :
    ∃ e : starImage H L ≃* PSL 4,
      Nonempty (NaturalDualCoordinates d.action.representation (starImage H L) e p.space) := by
  exact coordinates_of_natural_exclusions d r m p c
    (not_natural_quotient d r m p c)
    (fun k hk _ => not_repeated_natural d m p c k hk)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
