module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.AdequateSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents

/-!
# Small marked constituents from corrected adequate B.5

For the actual normal source component the Thompson actor has quasisimple
generalized Fitting subgroup. All nonquasisimple adequate alternatives
are excluded. In the exceptional outer-six-three case the normal cubic
factor centralizes the alternating component; self-centralization of F*
would place it in that disjoint component. No representation splitting
from the legacy exceptional clause is used.

The surviving actual B.5.1 action then constructs the marked V₂ constituent
used by15.3.31. The separate C.1.32/C.1.34 core classification is not asserted.

Source: Aschbacher–Smith B.5.1,B.5.6 and15.3.31, pp.99–105,1132.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open SourceRankOne.OriginalSource
universe u

/-- The actual adequate exceptional group shape cannot occur when F* is
quasisimple. Only group fields of that shape are used. -/
theorem quasisimple_source_of_adequate
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (hF : IsQuasisimple (generalizedFitting D)) (h : ProjectiveLine.AdequateSourceAlternative ρ) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D)) := by
  cases h with
  | trivial c => exact quasisimple_source_of_projectiveLineAlternative ρ hF (.trivial c)
  | quasisimple _ c => exact ⟨c⟩
  | symmetricThree c => exact quasisimple_source_of_projectiveLineAlternative ρ hF (.symmetricThree c)
  | twoFactors c => exact quasisimple_source_of_projectiveLineAlternative ρ hF (.twoFactors c)
  | hyperplane c => exact quasisimple_source_of_projectiveLineAlternative ρ hF (.hyperplane c)
  | outerSixThree c =>
    have hfirst := AdequateSelection.first_component c
    have he : c.first = generalizedFitting D := hfirst.eq_of_le
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hF⟩
      (component_le_generalizedFitting D c.first hfirst)
    have hcomm : c.second ≤ centralizer (c.first : Set D) := by
      intro b hb a ha
      have hh : c.product (⟨a,ha⟩,1) * c.product (1,⟨b,hb⟩) =
          c.product (1,⟨b,hb⟩) * c.product (⟨a,ha⟩,1) := by
        rw [←map_mul,←map_mul]
        simp only [Prod.mk_mul_mk,one_mul,mul_one]
      simpa only [Subtype.ext_iff,Subgroup.coe_mul,c.product_apply,Subgroup.coe_one,mul_one,one_mul]
        using hh
    have hle : c.second ≤ c.first := by
      rw [he] at hcomm ⊢
      exact hcomm.trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    have hz : c.second = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro b hb
      have hh : c.product (⟨b,hle hb⟩,1) = c.product (1,⟨b,hb⟩) := by
        apply Subtype.ext
        simp only [c.product_apply,Subgroup.coe_one,mul_one,one_mul]
      exact congrArg (fun x : c.first × c.second => (x.2 : D)) (c.product.injective hh) |>.symm
    let : Nontrivial c.second := c.secondEquiv.symm.injective.nontrivial
    exact ((nontrivial_iff_ne_bot c.second).mp inferInstance hz).elim

open Parabolics.Placement.ModelComparison EightGeometry.NaturalModule.Recognition
variable {G : Type u} [Group G] [Finite G]

/-- The marked small action is obtained from the proved corrected classifier
on the original Thompson action. -/
theorem smallAction_of_adequate_source (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hf : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hYL : d.Yplus ≤ c.L)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple I)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)] :
    SmallActionAlternative (componentAction d c hn hI hf P hP)
      (d.starImage I c.L)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  obtain ⟨hZI,hU,hFF,_⟩ := thompson_source_inputs d hSQTK hVT ⟨P,hP⟩ hf c
  let _ := hU
  have hF := thompson_fitting_quasisimple d c hn hI P hP (d.Z_le_S hVT)
  obtain ⟨hsource⟩ := quasisimple_source_of_adequate _ hF
    (SourceB5.classification.general _ _ _ hFF)
  rw [thompson_fitting_eq_component d c hn hI P hP (d.Z_le_S hVT)] at hsource
  have hc : Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 168 ∨
      Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 360 ∨
      Nat.card ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) = 6048 := by
    simpa only [Nat.card_congr (componentThompsonEquiv d c).toEquiv] using marked_star_card d c hm
  exact smallAction_of_movedAlternative d c hn hI hf P hP hZI hYL
    (movedSmallAlternative_of_projectiveLineConclusion _ _ hc hsource)
    (marked_intersection_card_of_star_card d c hm)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open EightGeometry.NaturalModule.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S) (hf : HasCharacteristicTwo I)
  (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = d.S)
  [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]

/-- The actual constituent and its V₂ marking require no universal FF premise. -/
theorem marked_alternative_of_adequate_source (hline : LineData d I) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hSQTK : IsSQTK KnownSimple.IsKnownSimple I)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    let ρ := componentAction d c hn hI hf S hS
    let Lstar := d.starImage I c.L
    let Pstar := (d.starImage I (d.M ⊓ c.L)).subgroupOf Lstar
    Nonempty (MarkedConstituent ρ Lstar (planeSpace d c) Pstar) ∧
      (IsIrrPlus ρ Lstar ⊤ ∨ ∃ e : ActionEquiv (ρ.comp Lstar.subtype) (repeated binaryNatural 2),
        Nonempty (BinaryDoubledLine ((planeSpace d c).map e.linearEquiv.toLinearMap)
          (Pstar.map e.groupEquiv.toMonoidHom))) := by
  apply marked_of_smallAction
  · exact SourceReduction.smallAction_of_adequate_source d c hn hI hf S hS hVT hYL hSQTK hm
  · exact hline.planeSpace_card d c S hS hYL
  · exact plane_stabilizer_eq_of_rank_one d c hn hI hf S hS hline hYL hRank hYRank
  · exact plane_disjoint_parabolic_fixed d c hn hI hf S hS hline hYL

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
