module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.LocalSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.CubicControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry

/-!
# Index and invariance of the actual component parabolic

After L = ⟨L^T⟩, set T₀ literally equal to T ∩ L. The subgroup
P = Y₀*T₀* has index three over T₀*: normality of Y₀ in Y₀T₀ and
|Y₀/O₂(Y₀)| = 3 bound the odd index, while an order-three element
survives the two-group quotient kernel. The prime index proves subgroup
minimality. Normalization of both factors proves T*-invariance.

The intersection formula P = (Y₀*T*) ∩ L* uses the previously proved
kernel-containing star-image formula; no general image-intersection
identity is assumed. These deductions precede the model-specific flag
identification and do not assert it.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1145, especially 15.3.49(k)–(l).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels


namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification

variable {G : Type*} [Group G] [Finite G]

private theorem sylow_index (H T : Subgroup G) (hT : IsSylowIn 2 T H) :
    ¬ 2 ∣ T.relIndex H := by
  obtain ⟨S, rfl⟩ := hT
  simpa only [relIndex, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
    using S.not_dvd_index

private theorem normal_sup_index (Y S : Subgroup G) [Y.Normal] :
    S.relIndex (Y ⊔ S) = S.relIndex Y := by
  have hmul : Y.relIndex S * S.relIndex (Y ⊔ S) = Y.relIndex S * S.relIndex Y := by
    calc
      _ = (S ⊓ Y).relIndex (Y ⊔ S) := by
        rw [← inf_relIndex_left (H := S) (K := Y)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (S ⊓ Y).relIndex Y * Y.relIndex (Y ⊔ S) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = _ := by simp [inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (index_ne_zero_of_finite : Y.relIndex S ≠ 0)) hmul

private theorem normalized_sup_index (Y S : Subgroup G)
    (hn : S ≤ normalizer (Y : Set G)) : S.relIndex (Y ⊔ S) = S.relIndex Y := by
  let J := Y ⊔ S
  let _ : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hn)
  have hi := normal_sup_index (Y.subgroupOf J) (S.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at hi
  exact hi

omit [Finite G] in
private theorem star_normalizes (H A B : Subgroup G)
    (hn : A ≤ normalizer (B : Set G)) :
    starImage H A ≤ normalizer (starImage H B : Set (H ⧸ pCore 2 H)) :=
  (map_mono ((comap_mono hn).trans (B.le_normalizer_comap H.subtype))).trans
    ((B.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

private theorem star_cubic (H Y : Subgroup G) (hYH : Y ≤ H)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    ∃ y : starImage H Y, orderOf y = 3 := by
  have hd : 3 ∣ Nat.card Y := hY ▸ (pCore 2 Y).index_dvd_card
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hd
  let f : Y →* H ⧸ pCore 2 H := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYH)
  have ho : orderOf (f y) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk y
      (hy ▸ (by decide : Nat.Coprime 2 3))).trans hy
  have hm : f y ∈ starImage H Y := ⟨⟨y, hYH y.property⟩, y.property, rfl⟩
  exact ⟨⟨f y, hm⟩, (Subgroup.orderOf_coe _).symm.trans ho⟩

private theorem normalized_sylow_index_three (H L Y T : Subgroup G)
    (hYH : Y ≤ H) (hYL : Y ≤ L)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hn : T ≤ normalizer (Y : Set G))
    (hs : IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L)) :
    (starImage H (T ⊓ L)).relIndex
      (ModelExclusions.componentParabolic H L Y T) = 3 := by
  let S := starImage H (T ⊓ L)
  let D := starImage H Y
  let P := ModelExclusions.componentParabolic H L Y T
  have hDP : D ≤ P := le_sup_left
  have hSP : S ≤ P := le_sup_right
  have hPL : P ≤ starImage H L :=
    sup_le (map_mono (comap_mono hYL)) (map_mono (comap_mono inf_le_right))
  have hS := hs.restrict hSP hPL
  have hi : S.relIndex P = S.relIndex D :=
    normalized_sup_index D S (star_normalizes H (T ⊓ L) Y (inf_le_left.trans hn))
  have hdiv : S.relIndex P ∣ Nat.card Y := by
    rw [hi]
    exact (relIndex_dvd_card S D).trans
      (((Y.subgroupOf H).card_map_dvd (QuotientGroup.mk' (pCore 2 H))).trans
        ((Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv).dvd))
  have hcard : Nat.card (pCore 2 Y) * 3 = Nat.card Y := by
    simpa only [Subgroup.index, hY] using (pCore 2 Y).card_mul_index
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  rw [← hcard, hn] at hdiv
  have hc : (S.relIndex P).Coprime 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr (sylow_index P S hS)).symm
  have hd3 : S.relIndex P ∣ 3 := (hc.pow_right n).dvd_of_dvd_mul_left hdiv
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with hone | hthree
  · have hDS : D ≤ S := hDP.trans (relIndex_eq_one.mp hone)
    obtain ⟨y, hy⟩ := star_cubic H Y hYH hY
    let x : S := ⟨y, hDS y.property⟩
    have hx : orderOf x = 3 := by
      rw [← Subgroup.orderOf_coe x, show (x : H ⧸ pCore 2 H) = y from rfl,
        Subgroup.orderOf_coe y, hy]
    have hc := (isSylowIn_iff.mp hS).1.orderOf_coprime (by decide : Nat.Coprime 2 3) x
    rw [hx] at hc
    exact (by decide : ¬ Nat.Coprime 3 3) hc |>.elim
  · exact hthree

omit [Finite G] in
private theorem minimal_of_index_three (S P : Subgroup G) (hSP : S ≤ P)
    (hi : S.relIndex P = 3) : S ⋖ P := by
  refine ⟨lt_of_le_of_ne hSP ?_, ?_⟩
  · intro he
    rw [he, relIndex_self] at hi
    contradiction
  · intro Q hSQ hQP
    have hm := relIndex_mul_relIndex S Q P hSQ.le hQP.le
    rw [hi] at hm
    have hp : (S.relIndex Q * Q.relIndex P).Prime := hm ▸ Nat.prime_three
    rcases (Nat.prime_mul_iff.mp hp) with h | h
    · exact hQP.not_ge (relIndex_eq_one.mp h.2)
    · exact hSQ.not_ge (relIndex_eq_one.mp h.2)

omit [Finite G] in
theorem parabolic_le_component (H L Y T : Subgroup G) (hYL : Y ≤ L) :
    ModelExclusions.componentParabolic H L Y T ≤ starImage H L :=
  sup_le (map_mono (comap_mono hYL)) (map_mono (comap_mono inf_le_right))

omit [Finite G] in
theorem parabolic_invariant (H L Y T : Subgroup G)
    (hTY : T ≤ normalizer (Y : Set G)) (hclosed : localSpan L T = L) :
    starImage H T ≤ normalizer
      (ModelExclusions.componentParabolic H L Y T : Set (H ⧸ pCore 2 H)) := by
  have hTL : T ≤ normalizer (L : Set G) :=
    hclosed ▸ le_normalizer_conjugateSpanBy L T
  have hTI : T ≤ normalizer (T ⊓ L : Subgroup G) :=
    (le_inf T.le_normalizer hTL).trans inf_normalizer_le_normalizer_inf
  exact (le_inf (star_normalizes H T Y hTY) (star_normalizes H T (T ⊓ L) hTI)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
open scoped Pointwise in
theorem parabolic_eq_intersection (H L Y T : Subgroup G)
    (hT : IsSylowIn 2 T H) (hYL : Y ≤ L) (hTY : T ≤ normalizer (Y : Set G)) :
    ModelExclusions.componentParabolic H L Y T =
      (starImage H Y ⊔ starImage H T) ⊓ starImage H L := by
  apply le_antisymm
  · exact le_inf (sup_le_sup le_rfl (map_mono (comap_mono inf_le_left)))
      (parabolic_le_component H L Y T hYL)
  · intro x hx
    have hxprod : x ∈ (starImage H Y : Set (H ⧸ pCore 2 H)) * starImage H T := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (star_normalizes H T Y hTY)]
      exact hx.1
    obtain ⟨y, hy, t, ht, rfl⟩ := hxprod
    have hyL : y ∈ starImage H L := (map_mono (comap_mono hYL)) hy
    have htL : t ∈ starImage H L := (mul_mem_cancel_left hyL).mp hx.2
    have htI : t ∈ starImage H (T ⊓ L) := by
      rw [starImage_inter_sylow H T L hT]
      exact ⟨ht, htL⟩
    exact mul_mem_sup hy htI

omit [Finite G] in
theorem reduced_data (H M L Y T : Subgroup G) (c : LocalControl H M Y T)
    (hgen : H = reducedOvergroup L Y T) (hclosed : localSpan L T = L)
    (hYL0 : Y ≤ localSpan L T) (hout : ¬ H ≤ M) :
    ModelExclusions.ReducedLocalData H M L Y T := by
  have hYL : Y ≤ L := hclosed ▸ hYL0
  have hgen' : H = L ⊔ T := by
    simpa only [reducedOvergroup, hclosed, ← sup_assoc, sup_eq_left.mpr hYL] using hgen
  refine ⟨?_, hYL, c.theta_eq.symm, c.sylow, c.t_le_m, ?_, hout, ?_⟩
  · simpa only [sup_eq_left.mpr hYL] using hgen'
  · rw [hgen']
    exact sup_le L.le_normalizer (hclosed ▸ le_normalizer_conjugateSpanBy L T)
  · intro K hYK hKH hK
    exact c.overgroups K hK hYK hKH

theorem parabolic_local (H M L Y T : Subgroup G) (c : LocalControl H M Y T)
    (hgen : H = reducedOvergroup L Y T) (hclosed : localSpan L T = L)
    (hYL0 : Y ≤ localSpan L T) (hL : (L.subgroupOf H).IsCComponent) :
    IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L) ∧
      ModelExclusions.componentParabolic H L Y T ≤ starImage H L ∧
      (starImage H (T ⊓ L)).relIndex (ModelExclusions.componentParabolic H L Y T) = 3 ∧
      starImage H (T ⊓ L) ⋖ ModelExclusions.componentParabolic H L Y T ∧
      starImage H T ≤ normalizer
        (ModelExclusions.componentParabolic H L Y T : Set (H ⧸ pCore 2 H)) := by
  have hLH : L ≤ H := hgen ▸ (le_conjugateSpanBy L T).trans le_sup_left
  have hYL : Y ≤ L := hclosed ▸ hYL0
  have hs := (component_inter_sylow H T L c.sylow hLH hL).2
  have hi := normalized_sylow_index_three H L Y T (hYL.trans hLH) hYL
    c.quotient_card c.normalizes hs
  exact ⟨hs, parabolic_le_component H L Y T hYL, hi,
    minimal_of_index_three _ _ le_sup_right hi,
    parabolic_invariant H L Y T c.normalizes hclosed⟩

omit [Finite G] in
theorem parabolic_solvable (H M L Y T : Subgroup G) (c : LocalControl H M Y T) :
    Group.IsSolvable (ModelExclusions.componentParabolic H L Y T) := by
  let I := M ⊓ H
  let _ := c.solvable_intersection
  let _ : Group.IsSolvable (I.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show I ≤ H from inf_le_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show I ≤ H from inf_le_right)).injective
  let _ : Group.IsSolvable (starImage H I) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)
  have hYI : Y ≤ I := c.theta_eq ▸ theta_le I
  have hTI : T ≤ I := le_inf c.t_le_m (isSylowIn_iff.mp c.sylow).2.1
  have hPI : ModelExclusions.componentParabolic H L Y T ≤ starImage H I :=
    sup_le (map_mono (comap_mono hYI))
      (map_mono (comap_mono (inf_le_left.trans hTI)))
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hPI)

/-- The same component equivalence transports the literal Sylow and its index. -/
theorem model_inputs {K D : Type*} [Group K] [Finite K] [Group D]
    (L S P : Subgroup K) (e : L ≃* D) (hs : IsSylowIn 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hi : S.relIndex P = 3) :
    ∃ Q : Sylow 2 D,
      (Q : Subgroup D) = (S.subgroupOf L).map e.toMonoidHom ∧
      (Q : Subgroup D) ≤ (P.subgroupOf L).map e.toMonoidHom ∧
      (Q : Subgroup D).relIndex ((P.subgroupOf L).map e.toMonoidHom) = 3 := by
  obtain ⟨R, hR⟩ := hs
  have hSR : S.subgroupOf L = (R : Subgroup L) := by
    rw [← hR]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_, ?_, ?_⟩
  · change (R : Subgroup L).map e.toMonoidHom = _
    rw [hSR]
  · change (R : Subgroup L).map e.toMonoidHom ≤ _
    rw [← hSR]
    exact map_mono (comap_mono hSP)
  · change ((R : Subgroup L).map e.toMonoidHom).relIndex _ = 3
    rw [← hSR, relIndex_map_map_of_injective _ _ e.injective,
      relIndex_subgroupOf hPL, hi]

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification
