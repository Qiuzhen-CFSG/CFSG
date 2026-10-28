module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First

/-!
# The distance-eight four-group in the original MS ambient group

Pull the actual H_alpha back along the amalgam embedding and include it from
the characteristic replacement into the original group. The preceding (4.4)
input and the first calculations (4.5.1) show that this subgroup is elementary
abelian of order four, lies in the original commutator core, and centralizes
the original component.

The replacement is only a normal subgroup of the original group. Centrality
in the replacement does not assert centrality in the original group. The last
lemma isolates the exact additional transport premise: centralization of the
original two-core. The binary MS input already gives O_2(J)L = J, so this
premise and the proved component centralization give centrality in J.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), (4.5.1), Section 7,
printed pp.890--896, 932--933; Aschbacher--Smith C.1.34(4), pp.136--137.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L T : Subgroup J} {h : Input κ L T} (t : InputSetup h)

/-- The literal replacement fixed factor, included in the original ambient group. -/
@[expose] def reducedCentralFour : Subgroup J :=
  ((H t.reduction.radical (alpha t.reduction.radical)).comap
    (embedM t.reduction.radical)).map t.reduction.overgroup.subtype

/-- The first source calculations give order four after the two injective maps. -/
theorem reducedCentralFour_card
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    Nat.card t.reducedCentralFour = 4 := by
  obtain ⟨p, first⟩ := DistanceEight.CoreFactors.Early.sourcePath_firstFacts_nonempty
    t.source common earlier (alpha t.reduction.radical) rfl
  have hcard : Nat.card (H t.reduction.radical (alpha t.reduction.radical)) = 4 := by
    simpa only [p.center_eq] using
      (first.forward 4 (by decide) (by decide) (by decide)).H_card
  rw [reducedCentralFour, card_map_of_injective t.reduction.overgroup.subtype_injective,
    ← card_map_of_injective (f := embedM t.reduction.radical)
      (embedM_injective t.reduction.radical),
    DistanceEight.H_alpha_comap_map t.reduction.radical
      (earlier.centrality _ rfl)]
  exact hcard

/-- The central-commutator argument survives inclusion in the original group. -/
theorem reducedCentralFour_elementary
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    IsElementaryAbelian 2 t.reducedCentralFour := by
  let := DistanceEight.H_alpha_comap_elementary_of_central t.reduction.radical
    common (earlier.centrality _ rfl)
  exact IsElementaryAbelian.map t.reduction.overgroup.subtype

/-- The characteristic replacement preserves the original commutator core. -/
theorem reducedCentralFour_le_commutatorCore
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reducedCentralFour ≤ commutatorCore L := by
  rw [← t.core_pullback]
  apply map_mono
  apply comap_mono
  exact (earlier.factor_inclusions common).1.trans inf_le_left

/-- The replacement contains the original component, which therefore fixes the factor. -/
theorem reducedCentralFour_centralizes_component
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reducedCentralFour ≤ centralizer (L : Set J) := by
  rintro x ⟨z, hz, rfl⟩
  apply mem_centralizer_iff.mpr
  intro l hl
  exact congrArg Subtype.val
    (mem_center_iff.mp
      (DistanceEight.H_alpha_comap_le_center t.reduction.radical
        (earlier.centrality _ rfl) hz)
      ⟨l, (show L ≤ t.reduction.overgroup from le_sup_left) hl⟩)

/-- Centrality in the original group follows once its original two-core fixes the factor. -/
theorem reducedCentralFour_le_center_of_centralizes_core
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (hc : t.reducedCentralFour ≤ centralizer (pCore 2 J : Set J)) :
    t.reducedCentralFour ≤ center J := by
  have htop : (⊤ : Subgroup J) ≤ centralizer (t.reducedCentralFour : Set J) := by
    rw [← h.core_sup_component]
    exact sup_le (le_centralizer_iff.mp hc)
      (le_centralizer_iff.mp (t.reducedCentralFour_centralizes_component earlier))
  exact centralizer_eq_top_iff_subset.mp (top_unique htop)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
