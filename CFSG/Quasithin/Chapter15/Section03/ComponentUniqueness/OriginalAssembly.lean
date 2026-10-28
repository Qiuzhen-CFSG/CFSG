module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OriginalSource.Complete
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.OriginalUniqueness

/-!
# Original component exclusions and the fixed-plane bound

The rank-one marked contradiction combines with the rank-two conclusion
at a minimal outside overgroup. This proves local uniqueness for either
choice in Hypothesis15.3.10, and the actual plane geometry supplies the literal
fixed-plane centralizer bound in15.3.45(3). The preceding15.3.25 and15.3.35 source conclusions
are retained for their independent producers.

Source: Aschbacher--Smith 15.3.35 and15.3.43--45, pp.1135,1139--1140.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original15.3.44 from the preceding characteristic-two and rank-two
source exclusions. The actual marked rank-one contradiction supplies15.3.43. -/
theorem source_unique_of_original_component_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h25 : SymmetricThreeShadow d.Yplus d.S →
      ∀ A ∈ d.Hplus, generalizedFitting A ≠ pCore 2 A)
    (h35 : ∀ I ∈ d.HplusMinimal, SymmetricThreeShadow d.Yplus d.S) :
    Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ d.S) d.M := by
  have hYM : d.Yplus ≤ d.M := by
    rcases d.choice with he | ⟨_, he⟩
    · rw [he]
      exact Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
    · rw [he]
      exact (map_subtype_le _).trans
        (inf_le_left.trans (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))
  exact unique_of_component_exclusions hM.1.1 hYM (inf_le_left.trans d.sylow_le) h35
    (fun I hI => RankOne.source_not_symmetricThreeShadow_of_original
      hG d hempty hM hu hmany h25 hI)

/-- Rechoosing only the subgroup in Hypothesis15.3.10 gives both applications
of15.3.44 required by15.3.45. All plane geometry is already discharged. -/
theorem source_fixedPlane_centralizer_le_of_original_component_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h25 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      SymmetricThreeShadow Yplus d.S →
      ∀ A ∈ outsideFamily Yplus d.S d.M, generalizedFitting A ≠ pCore 2 A)
    (h35 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      ∀ I ∈ minimalOutsideFamily Yplus d.S d.M, SymmetricThreeShadow Yplus d.S) :
    centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M := by
  apply fixedPlane_centralizer_le_of_local_uniqueness d
  intro Yplus hchoice
  let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
  exact source_unique_of_original_component_exclusions hG d' hempty hM hu hmany
    (h25 Yplus hchoice) (h35 Yplus hchoice)

end CFSG.Quasithin.Chapter15.Section03
