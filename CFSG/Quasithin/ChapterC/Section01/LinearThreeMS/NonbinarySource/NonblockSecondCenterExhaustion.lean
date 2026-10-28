module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SecondCenterExhaustion
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockSecondCenterImage
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockMovedRadical

/-!
# The second-center exhaustion criterion in the original nonblock source

The original field-four configuration supplies its whole natural or doubled
center internally, at one full SL₃ marking. A doubled-dual model of its second
central quotient then leaves exactly an elementary upper subgroup or the
whole core. This keeps the original c, chosen module D, constrained hf, full
quotient and all central attachments.

In the natural-center, nonabelian-upper branch, exhaustion supplies the
whole doubled-dual quotient. The existing moved-center application discharges
the radical inequalities for every supplied Sylow overgroup and constructs
MSData with simultaneous line and Sylow markings. No Hypothesis1223 is used.

These are conditional applications: the upper model and nonabelianity are
not inferred from the source. Constructing that model, excluding the elementary
upper and nonabelian doubled-center branches, and the general fourth row
remain C.1.34 obligations. Source: Aschbacher–Smith C.1.34–35, pp.136–138,
and original 4.3.8–10, pp.616–617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterExhaustion
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
open ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1<n) (hF : Nat.card F=2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e

/-- At a marking supplied internally by the genuine field-four source,
a doubled-dual second central quotient has elementary full preimage or
exhausts Q. The module-recognition premise remains explicit. -/
theorem source_upper_exhaustion (hfour : Nat.card F=4) (hna : ¬IsMulCommutative (Q c)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      (HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∨
        HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) ∧
      (HasSectionModel (K c) (secondCenterIn (Q c)) (U c) (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual) →
        IsElementaryAbelian 2 (secondCenterIn (Q c)) ∨
          (secondCenterIn (Q c)=Q c ∧ HasSectionModel (K c) (Q c) (U c)
            (linearThreeActor mark)
            ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual))) := by
  obtain ⟨mark,_,_,_,hm⟩ := DoubledCenter.source_nonabelian_center_models c D hf n hn hF e hfour hna
  have hm' : HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∨
      HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := hm.imp And.left id
  refine ⟨mark,hm',?_⟩
  intro hu
  exact ChapterC.LinearThreeMS.NonbinarySource.SecondCenterExhaustion.second_elementary_or_core_of_double_dual
    (T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)) mark hm' hu

omit [CharP F 2] in
/-- The whole natural center in the original source is its whole moved center. -/
private theorem natural_center_moved
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    ⁅U c,K c⁆=U c := by
  let hp := msPair_of_quotient c D hf n (by omega) hF e
  have hU : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (Q c)=U c := rfl
  have hinit := NaturalCenter.center_eq_initial hp hn e
    (by simpa only [ms_commutator_eq,hU] using hm)
  have hz : U c=initialMoved (K c) (c.I.pCoreIn 2) := by
    simpa only [ms_commutator_eq,hU] using hinit
  rw [hz]
  apply commutator_isPPerfect_idempotent (K c)
    (initialOmega (K c) (c.I.pCoreIn 2)) (component_twoPerfect hp hn)
  · rw [initialOmega_eq]
    exact IsElementaryAbelian.isPGroup 2 _
  · rw [initialOmega_eq]
    exact (le_sup_left : K c ≤ K c ⊔ c.I.pCoreIn 2).trans
      ((K c ⊔ c.I.pCoreIn 2 : Subgroup G).le_normalizer.trans
        ((normalizer_le_normalizer_characteristic_image
          (K c ⊔ c.I.pCoreIn 2 : Subgroup G) (pCore 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G))).trans
          (normalizer_le_normalizer_omegaCenterIn ((K c ⊔ c.I.pCoreIn 2 : Subgroup G).pCoreIn 2))))

/-- The original third alternative, for every supplied Sylow overgroup,
requires a doubled-dual second central quotient over its natural center,
with nonabelian full preimage. Exhaustion and all radical inequalities
are discharged here. -/
theorem module_alternatives_of_upper_sections
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (hu : HasSectionModel (K c) (secondCenterIn (Q c)) (U c) (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual))
    (hna : ¬IsMulCommutative (secondCenterIn (Q c)))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F e := by
  obtain ⟨_,hdual⟩ := ChapterC.LinearThreeMS.NonbinarySource.SecondCenterExhaustion.second_eq_core_of_nonabelian_double_dual
    (T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)) e (Or.inl hm) hu hna
  have hmove := natural_center_moved c D hf n hn hF e hm
  have hrad := MovedCenter.radical_inequality D hf n hn hF e (hmove.symm ▸ hm) P hP hRP
  unfold MSModuleAlternatives
  rw [ms_commutator_eq]
  exact Or.inr (Or.inr (Or.inl ⟨hm,hdual,hrad⟩))

omit hF e [Field F] [Finite F] [CharP F 2] in
/-- Feed the exhausted upper section to the existing MSData constructor,
retaining its simultaneous line/Sylow markings and literal radical inequalities. -/
theorem exists_msData_of_upper_sections
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree=n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (hu : HasSectionModel (K c) (secondCenterIn (Q c)) (U c) (linearThreeActor e)
      ((specialLinearNatural (k := F.Carrier) 3).dual.prod (specialLinearNatural 3).dual))
    (hna : ¬IsMulCommutative (secondCenterIn (Q c))) :
    ∃ d : MSData c n, d.field=F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model)=Matrix.PSL3.LinearThree.lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model)=Matrix.PSL3.LinearThree.unipotentSL d.field.Carrier := by
  have hF : Nat.card F.Carrier=2^n := F.card_eq.trans (congrArg (2^·) hdegree)
  obtain ⟨_,hdual⟩ := ChapterC.LinearThreeMS.NonbinarySource.SecondCenterExhaustion.second_eq_core_of_nonabelian_double_dual
    (T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)) e (Or.inl hm) hu hna
  have hmove := natural_center_moved c D hf n hn hF e hm
  exact MovedCenter.exists_msData_of_sections D hf n hn F hdegree e (hmove.symm ▸ hm) hdual

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterExhaustion
