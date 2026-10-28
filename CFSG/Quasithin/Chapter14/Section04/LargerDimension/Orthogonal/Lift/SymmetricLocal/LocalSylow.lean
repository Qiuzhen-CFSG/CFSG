module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Centralizers
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Normalizer
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.SylowNormalizerInvolutionImage

/-!
# The literal local Sylow witness from its quotient calculation

The centralizer-image comparison gives N_H(D) as the full preimage of
C_{H/O₂(H)}(i*): U and C_H(i modulo ⟨z⟩) both normalize D, and
D has image ⟨i*⟩. The commutator preimage retains the source centralizer
modulo the central line; surjectivity of the ordinary centralizer is not required.
Pulling back the Sylow calculation in that centralizer retains the exact
original Sylow T and constructs the hlocal witness used by the normalizer
promotion theorem. No conjugate replacement for T is made.

The quotient Sylow calculation remains a model premise. It must be
proved for the selected i in W^g≤T; arbitrary Sylow intersections with
centralizers need not be Sylow.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Centralizing i modulo the central line suffices to normalize D.
The conjugated involution differs by an element of ⟨z⟩, already in D. -/
theorem centralizerLift_normalized_by_centralizer_mod_center
    (U : Subgroup G) (z i : G)
    (hHU : centralizer ({z} : Set G) ≤ normalizer (U : Set G))
    (hUD : U ≤ normalizer (centralizerLift U z i : Set G)) :
    commutatorPreimage (centralizer ({z} : Set G)) (zpowers i) (zpowers z) ≤
      normalizer (centralizerLift U z i : Set G) := by
  let D := centralizerLift U z i
  let M := commutatorPreimage (centralizer ({z} : Set G)) (zpowers i) (zpowers z)
  have hM : M ≤ centralizer ({z} : Set G) := commutatorPreimage_le _ _ _
  have hZ : centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using
      (centralizer_le_normalizer (zpowers z : Set G))
  have hc : ⁅M,zpowers i⁆ ≤ zpowers z := commutator_commutatorPreimage_le _ _ _ hZ
  apply le_normalizer_iff.mpr
  intro a ha d hd
  have hai : (MulAut.conj a) i ∈ D := by
    have h := D.mul_mem (mem_sup_right (hc (commutator_mem_commutator ha (mem_zpowers i))))
      ((show zpowers i ≤ D from le_sup_right.trans le_sup_left) (mem_zpowers i))
    simpa only [commutatorElement_def, inv_mul_cancel_right, MulAut.conj_apply] using h
  have hI : (zpowers i).map (MulAut.conj a).toMonoidHom ≤ D := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hai
  have hU : U.map (MulAut.conj a).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (hHU (hM ha))
  have hZmap : (zpowers z).map (MulAut.conj a).toMonoidHom = zpowers z :=
    mem_normalizer_iff_map_conj_eq.mp (hZ (hM ha))
  have hm : D.map (MulAut.conj a).toMonoidHom ≤ D := by
    change (⁅U,zpowers i⁆ ⊔ zpowers i ⊔ zpowers z).map _ ≤ D
    rw [Subgroup.map_sup, Subgroup.map_sup, map_commutator, hU, hZmap]
    exact sup_le (sup_le ((commutator_mono le_rfl hI).trans
      (le_normalizer_iff_commutator_le_right.mp hUD)) hI) le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hd)

/-- The centralizer-image comparison turns the local normalizer into the
literal preimage of the quotient involution centralizer. -/
theorem lift_normalizer_quotient_preimage
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hi : orderOf i = 2)
    (hiz : i ∈ centralizer ({z} : Set G))
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (hout : i ∉ U)
    (hcompare : ((commutatorPreimage (centralizer ({z} : Set G))
        (zpowers i) (zpowers z)).subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) =
      centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) :
    (normalizer (centralizerLift U z i : Set G)).subgroupOf (centralizer ({z} : Set G)) =
      (centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))).comap
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) := by
  let H := centralizer ({z} : Set G)
  let C := H ⊓ centralizer ({i} : Set G)
  let D := centralizerLift U z i
  let iH : H := ⟨i,hiz⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let : IsElementaryAbelian 2 D := hD
  have hUH : U ≤ H := hUcore ▸ pCoreIn_le 2 H
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hiU : i ∈ normalizer (U : Set G) := hHU hiz
  have hDH : D ≤ H := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr
      ((D.le_centralizer hd) z (mem_sup_right (mem_zpowers z))).symm
  have hnorm : C ⊔ U ≤ normalizer (D : Set G) :=
    lift_normalized_by_residual_join_core U C z i hZ hiU
      (inf_le_left.trans hHU) inf_le_right hmoved
  have hUintr : U.subgroupOf H = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hUH]
    exact hUcore.symm
  have hB : ⁅U,zpowers i⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hDle : D ≤ U ⊔ zpowers i := sup_le (sup_le (hB.trans le_sup_left) le_sup_right)
    (hzU.trans le_sup_left)
  have hDmap : (D.subgroupOf H).map q = zpowers (q iH) := by
    apply le_antisymm
    · have hh := map_mono (f := q) (subgroupOf_mono H hDle)
      rw [subgroupOf_sup hUH (zpowers_le.mpr hiz), Subgroup.map_sup, hUintr] at hh
      have hk : (pCore 2 H).map q = ⊥ := by
        apply (Subgroup.map_eq_bot_iff _).mpr
        rw [QuotientGroup.ker_mk']
      have he : (zpowers i).subgroupOf H = zpowers iH := by
        apply map_injective H.subtype_injective
        rw [map_subgroupOf_eq_of_le (zpowers_le.mpr hiz), MonoidHom.map_zpowers]
        rfl
      simpa only [hk, he, MonoidHom.map_zpowers, bot_sup_eq] using hh
    · apply zpowers_le.mpr
      exact mem_map_of_mem q
        ((show zpowers i ≤ D from le_sup_right.trans le_sup_left) (mem_zpowers i))
  have hqi : orderOf (q iH) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have hiH : iH ^ 2 = 1 := Subtype.ext (by rw [← hi]; exact pow_orderOf_eq_one i)
      rw [hiH,map_one]
    · intro he
      have hc : iH ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).mp he
      exact hout (hUcore ▸ mem_map_of_mem H.subtype hc)
  rw [subgroupOf_normalizer_eq hDH]
  let M := commutatorPreimage H (zpowers i) (zpowers z)
  apply normalizer_eq_comap_involution_centralizer q (D.subgroupOf H) (M.subgroupOf H) iH hqi hDmap
  · rw [QuotientGroup.ker_mk', ← hUintr, ← subgroupOf_normalizer_eq hDH]
    exact subgroupOf_mono H (le_sup_right.trans hnorm)
  · rw [← subgroupOf_normalizer_eq hDH]
    exact subgroupOf_mono H (centralizerLift_normalized_by_centralizer_mod_center U z i
      hHU (le_sup_right.trans hnorm))
  · exact hcompare

/-- Pull the quotient Sylow calculation back to exactly the original T.
No Sylow conjugation or replacement occurs. -/
theorem lift_local_sylow_of_quotient
    (T : Sylow 2 G) (z i : G) (D : Subgroup G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiz : i ∈ centralizer ({z} : Set G))
    (hpre : (normalizer (D : Set G)).subgroupOf (centralizer ({z} : Set G)) =
      (centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))).comap
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))
    (hbar : let H := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 H)
      let B := centralizer ({q ⟨i,hiz⟩} : Set (H ⧸ pCore 2 H))
      ∃ P : Sylow 2 B, (P : Subgroup B) =
        (((T : Subgroup G).subgroupOf H).map q).subgroupOf B) :
    ∃ P : Sylow 2 (centralizer ({z} : Set G) ⊓ normalizer (D : Set G) : Subgroup G),
      (P : Subgroup (centralizer ({z} : Set G) ⊓ normalizer (D : Set G) : Subgroup G)) =
        (localSylow (T : Subgroup G) D).subgroupOf
          (centralizer ({z} : Set G) ⊓ normalizer (D : Set G)) := by
  let H := centralizer ({z} : Set G)
  let N := H ⊓ normalizer (D : Set G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := centralizer ({q ⟨i,hiz⟩} : Set (H ⧸ pCore 2 H))
  have hN : N.subgroupOf H = B.comap q := by
    rw [inf_subgroupOf_left]
    exact hpre
  obtain ⟨P,hP⟩ := hbar
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  obtain ⟨S,hS⟩ := exists_sylow_preimage_restriction q (QuotientGroup.mk'_surjective _)
    hk (T.subtype hTz) B P hP
  have hidx := S.not_dvd_index
  rw [hS] at hidx
  change ¬ 2 ∣ ((T : Subgroup G).subgroupOf H).relIndex (B.comap q) at hidx
  rw [← hN, relIndex_subgroupOf (show N ≤ H from inf_le_left)] at hidx
  have he : (localSylow (T : Subgroup G) D).subgroupOf N = (T : Subgroup G).subgroupOf N := by
    ext a
    exact and_iff_left a.property.2
  have hlocal : ¬ 2 ∣ ((localSylow (T : Subgroup G) D).subgroupOf N).index := by
    rw [he]
    exact hidx
  exact ⟨((T.isPGroup'.to_le inf_le_left).comap_subtype (K := N)).toSylow hlocal,rfl⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
