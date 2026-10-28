module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Stellmacher.BaumannMap
/-!
# Excluding the characteristic Baumann obstruction

Transport characteristic subgroups along the actual local inclusion. The
intermediate Baumann identity B.2.3(4) makes a characteristic subgroup of
Baum(O₂(P)) one of Baum(T_E). Its normality in K therefore puts K inside
the characteristic-normalizer closure controlled by M.

Source: Aschbacher–Smith, B.2.3(4), C.1.37(1), and 15.3.67(2).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
open Subgroup
open CFSG.Quasithin

private theorem characteristic_map_equiv
    {A B : Type*} [Group A] [Group B]
    (C : Subgroup A) (e : A ≃* B) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  rw [characteristic_iff_map_le]
  intro φ x hx
  rcases hx with ⟨y, hy, rfl⟩
  rcases hy with ⟨c, hc, rfl⟩
  let ψ : A ≃* A := e.trans (φ.trans e.symm)
  have hψC : C.map ψ.toMonoidHom ≤ C := (characteristic_iff_map_le.mp hC) ψ
  exact ⟨ψ c, hψC ⟨c, hc, rfl⟩, e.apply_symm_apply _⟩

/-- Source 67(2) excludes the genuine relative-normality alternative of C.1.37. -/
theorem no_characteristic_baumann_normal {G : Type*} [Group G] [Finite G]
    (K M T X : Subgroup G) (R : Subgroup K)
    (hBR : ChapterB.baumann T ≤ R.map K.subtype) (hRT : R.map K.subtype ≤ T)
    (hcontrol : characteristicNormalizerClosure (ChapterB.baumann T) ≤ M)
    (hXK : X ≤ K) (hXM : ¬ X ≤ M)
    (C : Subgroup (ChapterB.baumann R)) [C.Characteristic] (hC : C ≠ ⊥)
    (hn : (C.map (ChapterB.baumann R).subtype).Normal) : False := by
  have hB : (ChapterB.baumann R).map K.subtype = ChapterB.baumann T := by
    have hm := Stellmacher.baumann_map_injective K.subtype K.subtype_injective R
    change (ChapterB.baumann R).map K.subtype = ChapterB.baumann (R.map K.subtype) at hm
    exact hm.trans (ChapterB.lemma_B_2_3_4 T _ hBR hRT).symm
  let e : ChapterB.baumann R ≃* ChapterB.baumann T :=
    ((ChapterB.baumann R).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hB)
  let D := C.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv C e inferInstance
  have hD : D ≠ ⊥ := fun hb => hC ((C.map_eq_bot_iff_of_injective e.injective).mp hb)
  have hmap : D.map (ChapterB.baumann T).subtype =
      (C.map (ChapterB.baumann R).subtype).map K.subtype := by
    simp only [D, map_map]
    rfl
  have hKn : K ≤ normalizer (D.map (ChapterB.baumann T).subtype : Set G) := by
    rw [hmap]
    let := hn
    have hh := (C.map (ChapterB.baumann R).subtype).le_normalizer_map K.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact hXM (hXK.trans (hKn.trans
    ((normalizer_le_characteristicNormalizerClosure _ D hD).trans hcontrol)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
