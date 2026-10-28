module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.Normalizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Relative local structure of the component–Baumann product

The literal Y = L Baum(R) is normal in LT. Characteristic two passes to Y,
and the actual C-component remains a C-component there. The module normalizer
supplies SQTK, while the two-group supplement gives O²(Y) = L. All maps use
the original subgroup inclusions; no ambient subnormality of L is assumed.

OriginalUnitaryNoncentrality.PushingUp applies these facts as the local
hypotheses of the exceptional MS argument.
Source: Aschbacher–Smith C.1.31–37, pp.135–143; 13.3.10(2), pp.887–888.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- All local and residual hypotheses of MS1 hold in the actual
component--Baumann product; normality is relative to LT throughout. -/
theorem unitary_baumann_product_local
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G)) :
    let Y := L ⊔ ChapterB.baumann R
    IsSQTK KnownSimple.IsKnownSimple Y ∧
      generalizedFitting Y = pCore 2 Y ∧
      (L.subgroupOf Y).IsCComponent ∧
      pResidual 2 Y = L.subgroupOf Y := by
  intro Y
  let X := L ⊔ (T : Subgroup G)
  have hYX : Y ≤ X := sup_le le_sup_left (inf_le_left.trans (hRT.trans le_sup_right))
  have hXY : X ≤ normalizer (Y : Set G) := by
    apply sup_le (le_sup_left.trans Y.le_normalizer)
    exact (le_inf chosen.sylow_normalizes_component
      (hTR.trans (normalizer_le_normalizer_baumann R))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : (Y.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXY
  have hYN : Y ≤ normalizer (V : Set G) :=
    hYX.trans (sup_le chosen.normalizes hTV)
  have hlocal : IsTwoLocal (normalizer (V : Set G)) :=
    ⟨V,chosen.ne_bot,chosen.elementary.isPGroup,rfl⟩
  have hsq : IsSQTK KnownSimple.IsKnownSimple Y :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hYN)).mp
      ((h.qtke.twoLocal_sqtk hlocal).subgroup _)
  have hcharX : HasCharacteristicTwo X :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T)
      ⟨hmax.1.2.2,show (T : Subgroup G) ≤ X from le_sup_right⟩)
  have hcharY : HasCharacteristicTwo Y :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hYX)).mp
      (subnormal_core_selfCentralizing hcharX (Y.subgroupOf X)
        (inferInstance : (Y.subgroupOf X).Normal).isSubnormal)
  have hcomp : (L.subgroupOf Y).IsCComponent := by
    have hc := (hmax.1.1.subgroupOf
      (subgroupOf_mono X (show L ≤ Y from le_sup_left))).map_equiv (subgroupOfEquivOfLe hYX)
    have he : ((L.subgroupOf X).subgroupOf (Y.subgroupOf X)).map
        (subgroupOfEquivOfLe hYX).toMonoidHom = L.subgroupOf Y := by
      ext y
      rw [mem_map_equiv]
      rfl
    rwa [he] at hc
  have hLnorm : (L.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer
      (inf_le_left.trans (hRT.trans chosen.sylow_normalizes_component)))
  let := hLnorm
  have hperfect : IsPPerfect 2 (L.subgroupOf Y) :=
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1).of_surjective
      (subgroupOfEquivOfLe (show L ≤ Y from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ Y from le_sup_left)).symm.surjective
  refine ⟨hsq,generalizedFitting_eq_pCore_of_selfCentralizing 2 hcharY,hcomp,?_⟩
  apply pResidual_eq_of_isPPerfect_sup (L.subgroupOf Y)
    ((ChapterB.baumann R).subgroupOf Y) hperfect
    (T.isPGroup'.to_le (show ChapterB.baumann R ≤ (T : Subgroup G) from inf_le_left.trans hRT)).comap_subtype
  rw [←subgroupOf_sup (show L ≤ Y from le_sup_left)
    (show ChapterB.baumann R ≤ Y from le_sup_right),subgroupOf_self]
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
