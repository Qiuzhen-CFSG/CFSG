module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs.SubgroupTransport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.ExactDistanceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Frattini

/-!
# The distance-four sections on the original small MS pair

The genuine distance-four quotient has the entire core center as its kernel.
Its two dual factors and its natural center are transported through the
inclusion of the actual join L ∨ R, using the original component quotient
marking for both sections. This passage also transports the Frattini bound;
no action of the larger original group is inferred from replacement centrality.

The final application supplies the third C.1.34 alternative once the separate
radical-centralizer inequality is proved. That remaining source clause and
the distance-eight alternative stay with the full linear-three assembly
owner, qt-rank-two-ms93; this module does not assert the full classification.

Source: Meierfrankenfeld–Stellmacher (1993), (4.6), pp.901–912;
Aschbacher–Smith C.1.34(3), printed pp.136–137.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" =>
  CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- Both original C.1.34(3) sections, with one marking and no quotient or
conjugation-action premise beyond the genuine distance-four source data. -/
theorem SmallMSPair.distance_four_source_sections (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      let a := linearThreeActor e'
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
      HasSectionModel L (msCenter (msQ L R)) ⊥ a v ∧
        HasSectionModel L (msQ L R) (msCenter (msQ L R)) a (v.dual.prod v.dual) := by
  obtain ⟨hZ, hQ⟩ := t.sectionModels_of_distance_four common hb
  change HasSectionModel (L.subgroupOf (L ⊔ R))
    (msCenter (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)))) ⊥ _ _ at hZ
  rw [msQ_subgroupOf le_sup_left le_sup_right,
    centerIn_subgroupOf (msQ_le_join L R)] at hZ
  change HasSectionModel (L.subgroupOf (L ⊔ R))
    (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)))
    (msCenter (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)))) _ _ at hQ
  rw [msQ_subgroupOf le_sup_left le_sup_right,
    centerIn_subgroupOf (msQ_le_join L R)] at hQ
  let i := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let c := QuotientGroup.congr _ _ i.symm (pCore_map_iso 2 i.symm)
  let em := (h.binaryInput e).quotientEquiv.trans common.natural.marking
  let e' := c.trans em
  let a := linearThreeActor e'
  let v := Representation.specialLinearNatural (k := ZMod 2) 3
  have hactor : linearThreeActor em = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change em (QuotientGroup.mk' _ x) = em (c (QuotientGroup.mk' _ (i x)))
    change em (QuotientGroup.mk' _ x) = em (QuotientGroup.mk' _ (i.symm (i x)))
    rw [i.symm_apply_apply]
  rw [hactor] at hZ hQ
  refine ⟨e', ?_, ?_⟩
  · apply HasSectionModel.of_subgroupOf (J := L ⊔ R)
      (D := msCenter (msQ L R)) (E := ⊥) le_sup_left
      ((map_subtype_le (center (msQ L R))).trans (msQ_le_join L R)) bot_le a v
    simpa only [bot_subgroupOf] using hZ
  · exact HasSectionModel.of_subgroupOf (J := L ⊔ R)
      (D := msQ L R) (E := msCenter (msQ L R)) le_sup_left (msQ_le_join L R)
      ((map_subtype_le (center (msQ L R))).trans (msQ_le_join L R)) a
      (v.dual.prod v.dual) hQ

/-- The local distance-four Frattini bound holds in the literal original
commutator core after both injective inclusions. -/
theorem SmallMSPair.distance_four_frattini_le_center (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4) :
    frattiniIn (msQ L R) ≤ msCenter (msQ L R) := by
  let f := t.coreEquiv.trans (binaryCoreEquiv L R)
  have hh := BinaryMS.MS93.DistanceFour.core_frattini_le_center_of_distance_four common hb
  apply map_mono
  intro x hx
  rw [← frattini_map_equiv f] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (centerCongr f ⟨y, hh hy⟩).property

/-- The original nonabelian core discharges the common-source premises of the
distance-four section theorem. Only the remaining local source clause
R ≠ O₂(C(Ω₁Z(S))) remains in this branch of the full classification. -/
theorem SmallMSPair.distance_four_source (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : t.geometry.b t.reduction.radical = 4)
    (S : Subgroup G) (hineq : MSNotCentralizerCore L R S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L R).symm.injective
    simpa only [map_mul] using
      isMulCommutative_iff.mp hh ((binaryCoreEquiv L R).symm x)
        ((binaryCoreEquiv L R).symm y)
  obtain ⟨common⟩ := t.commonFacts hc'
  obtain ⟨e', hZ, hQ⟩ := h.distance_four_source_sections e t common hb
  exact ⟨e', Or.inr (Or.inr (Or.inl ⟨hZ, hQ, hineq⟩))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
