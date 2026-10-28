module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Defs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Elementary
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Self-centralization and assembly of the canonical fusion eight

The canonical fusion subgroup is already normal in the involution centralizer.
If it is elementary of order eight, its centralizer has no element of order
three: Sylow restriction would make the distinguished cubic subgroup centralize
all eight elements, contrary to the source fixed subgroup of order two. Its
centralizer is therefore a normal two-subgroup of H and lies in Q. The sharp
extraspecial abelian-subgroup bound then proves ambient self-centralization.

Relative quaternion normality gives exactly seven conjugates of z in Q.
The cubic action proves that their generated subgroup is elementary. The same
extraspecial bound forces that subgroup to have order eight; cardinality then
identifies its nonidentity elements with the literal fusion set. The final
theorem discharges both fusion-geometry premises from the original hypotheses,
without assuming that this subgroup is normal in G. This is the source's
fusion subgroup F; the intersection E = Q ∩ Qᵍ is a separate construction.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.3–2.7 and the opening proof of 4.1;
Aschbacher–Smith, I.4.6, `refs/quasithin.pdf`, printed p.417.
-/

namespace CFSG.Quasithin.Extraspecial32
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {z : G}

namespace Hypotheses

/-- The actual canonical fusion eight is self-centralizing without any
ambient-normality assumption. -/
public theorem centralizer_fusionCore_eq_of_elementary_card (h : Hypotheses z)
    (he : IsElementaryAbelian 2 (fusionCore z))
    (hc : Nat.card (fusionCore z) = 8) :
    centralizer (fusionCore z : Set G) = fusionCore z := by
  let : IsElementaryAbelian 2 (fusionCore z) := he
  let E := (fusionCore z).subgroupOf (Centralizer z)
  have hFH : fusionCore z ≤ Centralizer z := (fusionCore_le z).trans (coreInG_le z)
  let : E.Normal := h.fusionCore_normal_in_centralizer
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hFH
  have hE : Nat.card E = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv).trans hc
  have hEQ : E ≤ Core z := by
    rw [← coreInG_subgroupOf z]
    exact comap_mono (fusionCore_le z)
  have hzE : distinguished z ∈ E := h.involution_mem_fusionCore
  let C := centralizer (E : Set (Centralizer z))
  have hnot : ¬ 3 ∣ Nat.card C := by
    intro hd
    obtain ⟨T, hT⟩ := h.X.exists_subgroupOf_eq_of_normal C
    let S := (T : Subgroup C).map C.subtype
    have hSX : S ≤ h.X := by
      rw [show S = (T : Subgroup C).map C.subtype from rfl, hT]
      exact map_le_iff_le_comap.mpr le_rfl
    have hS : 3 ≤ Nat.card S := by
      rw [show S = (T : Subgroup C).map C.subtype from rfl,
        card_map_of_injective C.subtype_injective]
      exact Nat.le_of_dvd (Nat.card_pos (α := T)) (T.dvd_card_of_dvd_card hd)
    have hSXeq : S = (h.X : Subgroup (Centralizer z)) :=
      eq_of_le_of_card_ge hSX (by rw [h.sylow_three_card]; exact hS)
    have hXC : (h.X : Subgroup (Centralizer z)) ≤ C := by
      rw [← hSXeq]
      exact map_subtype_le _
    have hEl : E ≤ zpowers (distinguished z) := by
      rw [← h.fixed]
      refine le_inf hEQ ?_
      intro e he a ha
      exact (hXC ha e he).symm
    have hsmall := card_le_of_le hEl
    rw [hE, Nat.card_zpowers, h.distinguished_order] at hsmall
    omega
  have hC2 : IsPGroup 2 C := by
    apply IsPGroup.of_card_dvd_pow (n := 6)
    have hd := C.card_subgroup_dvd_card
    rw [h.centralizer_card] at hd
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr hnot).symm.dvd_of_dvd_mul_left
      (show Nat.card C ∣ 3 * 2 ^ 6 from hd)
  have hCQ : C ≤ Core z := by
    rw [h.core_eq_pCore]
    exact le_sSup ⟨inferInstance, hC2⟩
  let A := E.subgroupOf (Core z)
  let : IsExtraspecial 2 (Core z) := h.extraspecial
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hEQ
  have hZA : center (Core z) ≤ A := by
    intro q hq
    have hqz : (q : Centralizer z) ∈ zpowers (distinguished z) := by
      rw [← h.core_center_image]
      exact mem_map_of_mem (Core z).subtype hq
    exact zpowers_le.mpr hzE hqz
  have hA : Nat.card A = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans hE
  have hAC := extraspecial_two_centralizer_eq_of_card_sq A hZA (by
    rw [hA, h.core_card]
    norm_num)
  have hCE : C ≤ E := by
    intro c hcc
    let q : Core z := ⟨c, hCQ hcc⟩
    have hq : q ∈ centralizer (A : Set (Core z)) := by
      intro a ha
      exact Subtype.ext (hcc a ha)
    rw [hAC] at hq
    exact hq
  apply le_antisymm
  · intro c hcc
    have hcH : c ∈ Centralizer z :=
      mem_centralizer_singleton_iff.mpr (hcc z h.involution_mem_fusionCore).symm
    apply hCE (show (⟨c, hcH⟩ : Centralizer z) ∈ C from ?_)
    intro e he
    exact Subtype.ext (hcc e he)
  · exact (fusionCore z).le_centralizer

/-- The two remaining fusion-geometry premises supply every field of the
canonical fusion-eight contract, including its exact fusion set and centralizer. -/
public theorem fusionEightData_of_seven_of_elementary (h : Hypotheses z)
    (hs : Nat.card {x : G // x ∈ coreInG z ∧ IsConj z x} = 7)
    (he : IsElementaryAbelian 2 (fusionCore z)) : FusionEightData z := by
  let : IsElementaryAbelian 2 (fusionCore z) := he
  let S : Set G := insert 1 {x : G | x ∈ coreInG z ∧ IsConj z x}
  have hone : (1 : G) ∉ {x : G | x ∈ coreInG z ∧ IsConj z x} := by
    intro hx
    have hz := isConj_one_left.mp hx.2
    have ho := h.involution
    rw [hz, orderOf_one] at ho
    omega
  have hS : S.ncard = 8 := by
    change (insert (1 : G) {x : G | x ∈ coreInG z ∧ IsConj z x}).ncard = 8
    rw [Set.ncard_insert_of_notMem hone]
    change Nat.card {x : G // x ∈ coreInG z ∧ IsConj z x} + 1 = 8
    omega
  have hSF : S ⊆ (fusionCore z : Set G) := by
    rintro x (rfl | hx)
    · exact (fusionCore z).one_mem
    · exact subset_closure hx
  let A := (fusionCore z).subgroupOf (coreInG z)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (fusionCore_le z)
  let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
  have hZA : center (coreInG z) ≤ A := by
    intro q hq
    have hqz : (q : G) ∈ zpowers z := by
      rw [← h.coreInG_center_image]
      exact mem_map_of_mem (coreInG z).subtype hq
    exact zpowers_le.mpr h.involution_mem_fusionCore hqz
  have hA : Nat.card A = Nat.card (fusionCore z) :=
    Nat.card_congr (subgroupOfEquivOfLe (fusionCore_le z)).toEquiv
  have hbound := extraspecial_two_abelian_card_sq_le A hZA
  rw [hA, h.coreInG_card] at hbound
  have hFle : Nat.card (fusionCore z) ≤ 8 := by nlinarith
  have hset : S = (fusionCore z : Set G) :=
    Set.eq_of_subset_of_ncard_le hSF (by
      rw [hS]
      exact hFle)
  have hcard : Nat.card (fusionCore z) = 8 := by
    change (fusionCore z : Set G).ncard = 8
    rw [← hset, hS]
  refine ⟨he, hcard, ?_, h.centralizer_fusionCore_eq_of_elementary_card he hcard⟩
  intro x hx hx1
  have hxS : x ∈ S := hset ▸ hx
  rcases hxS with hx1' | hx
  · exact (hx1 hx1').elim
  · exact hx.2

/-- The canonical fusion subgroup is a self-centralizing elementary eight
in the normal-quaternion branch. Normality of the quaternion subgroups is
relative to the involution centralizer; ambient normality of the fusion
subgroup is not needed. -/
public theorem fusionEightData_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) : FusionEightData z := by
  have hs := h.fusion_conjugates_card_of_quaternion_normal hn
  exact h.fusionEightData_of_seven_of_elementary hs (h.fusionCore_elementary_of_seven hs)

end Hypotheses
end CFSG.Quasithin.Extraspecial32
