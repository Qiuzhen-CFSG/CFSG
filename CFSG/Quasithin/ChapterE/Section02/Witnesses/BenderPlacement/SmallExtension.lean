module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallAutomizer
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.GeneralizedFitting.CubicResidualOrder
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Extension of the small marked pair across the two-core

The marked pair supplements the ambient two-core when its quotient has order six
and the ambient quotient has order at most six. The ambient two-core normalizes
the pair, so the pair is the full conjugate span and its core is normalized by
the ambient actor. This discharges the cyclic-residual branch of the extension
argument in Aschbacher--Smith, *The Classification of Quasithin Groups*, E.2.17.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.QuotientLift
variable {H : Type*} [Group H] [Finite H]
  {T : Sylow 2 H} {M V : Subgroup H}

omit [Finite H] in
theorem Pair.normal_span_of_twoCore_supplement (w : Pair T M V)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : w.subgroup ⊔ pCore 2 H = ⊤) :
    w.subgroup.Normal ∧ conjugateSpanBy V ⊤ = w.subgroup ∧
      (T : Subgroup H) ≤ normalizer (w.subgroup.pCoreIn 2 : Set H) := by
  have hg : V ⊔ V.map (MulAut.conj (w.conjugator : H)).toMonoidHom = w.subgroup := by
    have he := congrArg (Subgroup.map w.subgroup.subtype) w.generate
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le w.le] at he
    have hm : ((V.subgroupOf w.subgroup).map
        (MulAut.conj w.conjugator).toMonoidHom).map w.subgroup.subtype =
        V.map (MulAut.conj (w.conjugator : H)).toMonoidHom := by
      rw [map_map]
      have hc : w.subgroup.subtype.comp (MulAut.conj w.conjugator).toMonoidHom =
          (MulAut.conj (w.conjugator : H)).toMonoidHom.comp w.subgroup.subtype := by
        ext x; rfl
      rw [hc, ←map_map, map_subgroupOf_eq_of_le w.le]
    rw [hm, ←MonoidHom.range_eq_map, range_subtype] at he
    exact he
  have hNI : (⊤ : Subgroup H) ≤ normalizer (w.subgroup : Set H) := by
    rw [←hgen]
    exact sup_le w.subgroup.le_normalizer
      (hg ▸ ChapterE.twoCore_le_normalizer_conjugate_join T V hTV (w.conjugator : H))
  have hn : w.subgroup.Normal := normalizer_eq_top_iff.mp (top_unique hNI)
  have hspan : conjugateSpanBy V ⊤ = w.subgroup := by
    apply le_antisymm (conjugateSpanBy_le w.le hNI)
    rw [←hg]
    apply sup_le (le_conjugateSpanBy V ⊤)
    rintro x ⟨v, hv, rfl⟩
    exact subset_closure ⟨(w.conjugator : H), mem_top _, v, hv, rfl⟩
  exact ⟨hn,hspan,le_top.trans (hNI.trans
    (normalizer_le_normalizer_characteristic_image w.subgroup (pCore 2 w.subgroup)))⟩

theorem Pair.twoCore_supplement_of_quotient_card_bound (w : Pair T M V)
    (hH : Nat.card (H ⧸ pCore 2 H) ≤ 6)
    (hI : Nat.card (w.subgroup ⧸ pCore 2 w.subgroup) = 6) :
    w.subgroup ⊔ pCore 2 H = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := q.comp w.subgroup.subtype
  have hk : f.ker = (pCore 2 H).comap w.subgroup.subtype := by
    ext x; simp [f, q]; rfl
  have hkle : f.ker ≤ pCore 2 w.subgroup := by
    rw [hk]
    exact le_sSup ⟨inferInstance,
      pCore_isPGroup.comap_of_injective w.subgroup.subtype w.subgroup.subtype_injective⟩
  have hd : 6 ∣ Nat.card f.range := by
    have hh := index_dvd_of_le hkle
    rw [index_ker] at hh
    change Nat.card (w.subgroup ⧸ pCore 2 w.subgroup) ∣ Nat.card f.range at hh
    rw [hI] at hh
    exact hh
  have hcard : Nat.card f.range = 6 := by
    have hlo := Nat.le_of_dvd Nat.card_pos hd
    have hhi := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
    omega
  have hr : f.range = ⊤ := eq_top_of_card_eq f.range (by
    have hhi := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
    omega)
  have hm : w.subgroup.map q = ⊤ := by
    simpa only [f,MonoidHom.range_comp,range_subtype] using hr
  have he := congrArg (Subgroup.comap q) hm
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
end CFSG.Quasithin.ChapterE.Witnesses.QuotientLift


namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {N W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}

theorem OriginalWitness.small_normal_span_of_cubic_residual
    (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk))
    (hR : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3) :
    w.pair.subgroup.Normal ∧ conjugateSpanBy W ⊤ = w.pair.subgroup ∧
      Nonempty (QuaternionCentralProductData (w.pair.subgroup.pCoreIn 2)) ∧
      U = w.pair.subgroup.pCoreIn 2 ⊔ (U ⊓ centralizer (W : Set H)) ∧
      w.pair.subgroup.pCoreIn 2 ⊓ centralizer (W : Set H) =
        w.pair.subgroup.pCoreIn 2 ⊓ W ∧
      U ≤ normalizer (w.pair.subgroup.pCoreIn 2 : Set H) ∧
      ⁅U ⊓ centralizer (W : Set H), w.pair.subgroup.pCoreIn 2⁆ ≤
        w.pair.subgroup.pCoreIn 2 ⊓ W := by
  have hc := w.small_quaternion_core hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  obtain ⟨e⟩ := hc.2.2.2.1
  have hI : Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) = 6 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hQ : pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have he := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _)
      (show IsPGroup 2 q.ker by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    have hm := congrArg (map q) he
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  have hH := card_le_six_of_core_free_cubic_residual hQ hR
  have hgen := w.pair.twoCore_supplement_of_quotient_card_bound hH hI
  have hnorm := w.pair.normal_span_of_twoCore_supplement hSW hgen
  let := hnorm.1
  have hUP : U ≤ normalizer (w.pair.subgroup.pCoreIn 2 : Set H) :=
    (show U ≤ normalizer (w.pair.subgroup : Set H) by rw [normalizer_eq_top]; exact le_top).trans
      (normalizer_le_normalizer_characteristic_image w.pair.subgroup (pCore 2 w.pair.subgroup))
  exact ⟨hnorm.1, hnorm.2.1, hc.1, hc.2.1, hc.2.2.1, hUP, hc.2.2.2.2 hUP⟩
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
