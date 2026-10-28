module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.MarkTransport
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Lifting the marked parabolic signalizer argument

A relatively normal C-component K containing Y retains its marked elementary
five-kernel in the actual quotient of KR by O₂(KR). The component quotient
isomorphism identifies K/O₂(K) with its image, while the two-group supplement
R makes the remaining quotient a two-group. The proved PSL₃(5) recognition
and automorphism signalizer theorem then kills the image of R.

This proves R ≤ O₂(KR) without assuming that K normalizes R. The reverse
containment for the radical construction is in `Normalizers.Basic`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.513, final paragraph of the normalizer claim.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The marked five-kernel forces a normalized two-subgroup into the core
of the join with its containing component. -/
theorem radical_le_join_core_of_marked_five
    (K R N Y P : Subgroup G) (hK : K ∈ cComponentsIn N)
    (hKn : (K.subgroupOf N).Normal) (hRN : R ≤ N)
    (hR : IsPGroup 2 R) (hYK : Y ≤ K) (hPY : P ≤ Y)
    (hPR : P ≤ normalizer (R : Set G))
    (emodel : XiQuotient K ≃* Matrix.PSL3.RadicalParabolicTwoSignalizers.Model)
    (hmark : MarkedFiveExtension (((Y.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)))) (((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))))) :
    R ≤ (K ⊔ R).pCoreIn 2 := by
  let H := K ⊔ R
  let q := QuotientGroup.mk' (pCore 2 H)
  let Kbar := (K.subgroupOf H).map q
  let Rbar := (R.subgroupOf H).map q
  have hHN : H ≤ N := sup_le hK.1 hRN
  have hcomp : (K.subgroupOf H).IsCComponent :=
    hK.2.subgroupOf_of_le le_sup_left hHN
  have hHK : H ≤ normalizer (K : Set G) :=
    hHN.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKn)
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHK
  let : Kbar.Normal := (inferInstance : (K.subgroupOf H).Normal).map q
    (QuotientGroup.mk'_surjective _)
  let e := componentQuotientEquiv (show K ≤ H from le_sup_left) hcomp
  have hm := hmark.map e.toMonoidHom e.injective
  let B := (((Y.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)))).map e.toMonoidHom
  let Q := (((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)))).map e.toMonoidHom
  have hQmap : Q.map Kbar.subtype = ((P.subgroupOf H).map q) :=
    componentQuotientEquiv_map_subgroup (hPY.trans hYK) le_sup_left hcomp
  have hRbar : IsPGroup 2 Rbar := hR.comap_subtype.map q
  have hsup : Rbar ⊔ Kbar = ⊤ := by
    rw [← Subgroup.map_sup]
    have hs : R.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right),
        map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
        ← MonoidHom.range_eq_map, range_subtype]
      exact sup_comm R K
    rw [hs, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 (XiQuotient H ⧸ Kbar) :=
    quotient_isPGroup_of_sup_eq_top Rbar Kbar hRbar hsup
  have hnorm : Q.map Kbar.subtype ≤ normalizer (Rbar : Set (XiQuotient H)) := by
    rw [hQmap]
    apply le_trans (map_mono (show P.subgroupOf H ≤
      normalizer (R.subgroupOf H : Set H) from ?_))
      ((R.subgroupOf H).le_normalizer_map q)
    rw [← subgroupOf_normalizer_eq (show R ≤ H from le_sup_right)]
    exact comap_mono hPR
  obtain ⟨hQB, hQelem, hQnormal, ⟨equot⟩⟩ := hm
  let : (Q.subgroupOf B).Normal := hQnormal
  have hcard : Nat.card Q = 25 := by
    obtain ⟨ep⟩ := hQelem
    rw [Nat.card_congr ep.toEquiv]
    change Nat.card (Fin 2 → ZMod 5) = 25
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    decide
  have helem : IsElementaryAbelian 5 Q := by
    obtain ⟨ep⟩ := hQelem
    refine
      { toIsMulCommutative := ⟨⟨fun a b => ep.injective (by
          simp only [map_mul]
          exact mul_comm (ep a) (ep b))⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro a
    apply ep.injective
    rw [map_pow, map_one]
    change 5 • (ep a).toAdd = 0
    exact ZModModule.char_nsmul_eq_zero 5 (ep a).toAdd
  have hbot : Rbar = ⊥ :=
    Matrix.PSL3.RadicalParabolicTwoSignalizers.twoSignalizer_eq_bot_of_markedSubgroup
      Kbar (e.symm.trans emodel) hquot (pCore_quotient_pCore_eq_bot 2)
      B Q hQB helem hcard equot Rbar hRbar hnorm
  have hle : R.subgroupOf H ≤ pCore 2 H := by
    have hh := (Subgroup.map_eq_bot_iff (R.subgroupOf H)).mp hbot
    simpa only [q, QuotientGroup.ker_mk'] using hh
  have hh := map_mono (f := H.subtype) hle
  change R ≤ (pCore 2 H).map H.subtype
  simpa only [map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)] using hh

end CFSG.Quasithin.Chapter1.RadicalNormalizers
