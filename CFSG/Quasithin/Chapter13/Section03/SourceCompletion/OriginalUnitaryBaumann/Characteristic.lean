module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.Normalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs

/-!
# Characteristic-subgroup and core-normalizer control for the unitary product

A characteristic subgroup of Baum(R) normal in L Baum(R) is normalized by
T, since T normalizes R. Uniqueness over LT therefore turns Baumann-normalizer
escape into the literal MS3 condition inside L Baum(R). Separately, V lies
in its nontrivial two-core, and that core is normal in LT, giving the core's
ambient normalizer bound used at the end of printed p.888.

Both conclusions are applied to the original contrary case in
OriginalUnitaryNoncentrality.PushingUp. The block reconstruction and the
normalizer bound for the whole Baumann subgroup remain separate steps.
Source: Aschbacher–Smith C.1.31, C.1.37, and 13.3.10(2), pp.135,143,888.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (hc : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  exact ⟨b y,(characteristic_iff_le_comap.mp hc b) hy,e.apply_symm_apply _⟩

/-- A characteristic subgroup normal in L Baum(R) is already normal in LT:
T normalizes R, hence Baum(R) and all its characteristic subgroups. -/
theorem unitary_baumann_product_characteristic
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hout : ¬ normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G)) :
    ChapterC.MSCharacteristicCondition
      ((ChapterB.baumann R).subgroupOf (L ⊔ ChapterB.baumann R)) := by
  intro C hC hne hn
  let B := ChapterB.baumann R
  let Y := L ⊔ B
  let S := B.subgroupOf Y
  let f : S ≃* B := subgroupOfEquivOfLe (show B ≤ Y from le_sup_right)
  let D := C.map f.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv f C hC
  have hDne : D ≠ ⊥ := fun hz => hne ((C.map_eq_bot_iff_of_injective f.injective).mp hz)
  have he : D.map B.subtype = (C.map S.subtype).map Y.subtype := by
    rw [map_map,map_map]
    rfl
  have hYN : Y ≤ normalizer (D.map B.subtype : Set G) := by
    rw [he]
    have hm := (C.map S.subtype).le_normalizer_map Y.subtype
    let := hn
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hm
  have hTN : (T : Subgroup G) ≤ normalizer (D.map B.subtype : Set G) :=
    (hTR.trans (normalizer_le_normalizer_baumann R)).trans
      (normalizer_le_normalizer_characteristic_image B D)
  exact hout (unitary_baumann_normalizer_of_characteristic h chosen hmax eL R
    (hRT.trans le_sup_right) D hDne (sup_le (le_sup_left.trans hYN) hTN))

/-- The actual product core is nontrivial and normal in LT, so its full
ambient normalizer is controlled before invoking the block alternative. -/
theorem unitary_baumann_core_normalizer
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hVB : V ≤ ChapterB.baumann R) :
    normalizer ((L ⊔ ChapterB.baumann R).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) := by
  let Y := L ⊔ ChapterB.baumann R
  have hYX : Y ≤ L ⊔ (T : Subgroup G) :=
    sup_le le_sup_left (inf_le_left.trans (hRT.trans le_sup_right))
  have hYN : Y ≤ normalizer (V : Set G) := hYX.trans (sup_le chosen.normalizes hTV)
  have hVQ : V ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes chosen.elementary.isPGroup
    (hVB.trans le_sup_right) hYN
  have hQne : Y.pCoreIn 2 ≠ ⊥ := fun hz => chosen.ne_bot (le_bot_iff.mp (hVQ.trans_eq hz))
  have hXY : L ⊔ (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    apply sup_le (le_sup_left.trans Y.le_normalizer)
    exact (le_inf chosen.sylow_normalizes_component
      (hTR.trans (normalizer_le_normalizer_baumann R))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact chosen.normal_subgroup_normalizer_le
    (unitary_original_hypothesis1223 h hmax eL).toHypothesis1221
    ((pCoreIn_le 2 Y).trans hYX) hQne
    (hXY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
