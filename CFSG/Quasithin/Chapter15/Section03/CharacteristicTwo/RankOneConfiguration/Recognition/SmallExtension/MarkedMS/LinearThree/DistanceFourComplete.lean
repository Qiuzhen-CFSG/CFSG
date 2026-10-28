module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceFourOriginalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFourMovement

/-!
# The complete original distance-four alternative of C.1.34

Transport the proved replacement movement through the literal inclusion of
L join R. Sylow-fixed central correction makes its moving component element
centralize the original Sylow omega-center. Equality of R with that
centralizer's two-core would force the element to normalize R and hence its
characteristic replacement, a contradiction.

The complete source alternative retains one marking for the natural center
and the doubled-dual quotient. Nonabelianness constructs CommonFacts, and
there is no remaining movement or radical-centralizer premise. Full C.1.34
and the linearThree field remain with qt-rank-two-ms93, which must still
complete the distance-eight branch and discharge its fixed-factor input.

Source: Aschbacher--Smith C.1.34(3), printed pp.136--137;
Meierfrankenfeld--Stellmacher (1993), pp.831, 903.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R S : Subgroup G}

/-- The characteristic replacement is moved by a component element fixing
the original Sylow-fixed center. All subgroups and actions are literal. -/
theorem SmallMSPair.distance_four_replacement_movement (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    ¬ L ⊓ centralizer (msCenter (msQ L R) ⊓ centralizer (S : Set G) : Set G) ≤
      normalizer (t.reduction.ambient.map (L ⊔ R).subtype : Set G) := by
  let J := L ⊔ R
  obtain ⟨P,hP⟩ := hS
  have hSP : S.subgroupOf J = (P : Subgroup J) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hRP : R.subgroupOf J ≤ (P : Subgroup J) := hSP ▸ comap_mono hRS
  have hm := t.distance_four_replacement_movement common hb P hRP
  rw [msQ_subgroupOf le_sup_left le_sup_right,
    centerIn_subgroupOf (msQ_le_join L R)] at hm
  intro hn
  apply hm
  intro l hl
  have hlG : (l : G) ∈ L ⊓ centralizer
      (msCenter (msQ L R) ⊓ centralizer (S : Set G) : Set G) := by
    refine ⟨hl.1,?_⟩
    intro x hx
    have hxJ : x ∈ J := (map_subtype_le (center (msQ L R))).trans (msQ_le_join L R) hx.1
    let y : J := ⟨x,hxJ⟩
    have hy : y ∈ (msCenter (msQ L R)).subgroupOf J ⊓ centralizer (P : Set J) := by
      refine ⟨hx.1,?_⟩
      intro p hp
      apply Subtype.ext
      exact hx.2 p (hP ▸ mem_map_of_mem J.subtype hp)
    exact congrArg Subtype.val (hl.2 y hy)
  have hh := (Subgroup.le_normalizer_comap J.subtype) (hn hlG)
  rwa [comap_map_eq_self_of_injective J.subtype_injective] at hh

/-- The literal C.1.34(3) radical inequality, with its original Sylow and radical. -/
theorem SmallMSPair.distance_four_not_centralizer_core (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    MSNotCentralizerCore L R S :=
  h.distance_four_not_centralizer_core_of_replacement_movement e t common hb hS
    (h.distance_four_replacement_movement e t common hb hS hRS)

/-- The complete third source alternative, without an extra movement or
radical-centralizer premise and with one marking for both sections. -/
theorem SmallMSPair.distance_four_source_complete (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : t.geometry.b t.reduction.radical = 4)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv L R).symm x) ((binaryCoreEquiv L R).symm y)
  obtain ⟨common⟩ := t.commonFacts hc'
  exact h.distance_four_source_of_replacement_movement e t common hb hS
    (h.distance_four_replacement_movement e t common hb hS hRS)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS